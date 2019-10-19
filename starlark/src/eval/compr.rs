// Copyright 2019 The Starlark in Rust Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! List/dict/set comprenension evaluation.

use crate::eval::{eval_expr, make_set, set_expr, t, EvalException, EvalResult, EvaluationContext};
use crate::syntax::ast::AssignTargetExpr;
use crate::syntax::ast::AstAssignTargetExpr;
use crate::syntax::ast::AstClause;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::Clause;
use crate::syntax::ast::Expr;
use crate::syntax::ast::ToAst;
use crate::values::dict::Dictionary;
use crate::values::{TypedValue, Value};
use codemap::{Span, Spanned};
use codemap_diagnostic::Diagnostic;
use std::collections::HashMap;
use std::iter;

/// For clause followed by zero or more if clauses.
///
/// Each `for` clause defines a scope while `if` doesn't.
#[derive(Debug, Clone)]
pub struct ClauseForCompiled {
    var: AstAssignTargetExpr,
    over: AstExpr,
    ifs: Vec<AstExpr>,
    local_names_to_indices: HashMap<String, usize>,
}

impl ClauseForCompiled {
    fn to_raw<'a>(&'a self) -> impl Iterator<Item = AstClause> + 'a {
        iter::once(
            Clause::For(self.var.clone(), self.over.clone())
                .to_ast(self.var.span.merge(self.over.span)),
        )
        .chain(
            self.ifs
                .iter()
                .map(|ifc| Clause::If(ifc.clone()).to_ast(ifc.span)),
        )
    }

    fn compiled_to_raw(clauses: &[ClauseForCompiled]) -> Vec<AstClause> {
        clauses.iter().flat_map(ClauseForCompiled::to_raw).collect()
    }

    fn compile_clause(clause: ClauseForCompiled) -> Result<ClauseForCompiled, Diagnostic> {
        let ClauseForCompiled {
            var,
            over,
            ifs,
            mut local_names_to_indices,
        } = clause;
        debug_assert!(local_names_to_indices.is_empty());
        AssignTargetExpr::collect_locals_from_assign_expr(&var, &mut local_names_to_indices);
        let var = AssignTargetExpr::compile(var)?;
        let over = Expr::compile(over)?;
        let ifs = ifs
            .into_iter()
            .map(|expr| {
                let expr = Expr::transform_locals_to_slots(expr, &local_names_to_indices);
                let expr = Expr::compile(expr)?;
                Ok(expr)
            })
            .collect::<Result<_, _>>()?;
        Ok(ClauseForCompiled {
            var,
            over,
            ifs,
            local_names_to_indices,
        })
    }

    fn compile_clauses(clauses: Vec<AstClause>) -> Result<Vec<ClauseForCompiled>, Diagnostic> {
        let mut compiled: Vec<ClauseForCompiled> = Vec::new();
        for clause in clauses {
            match clause.node {
                Clause::For(var, over) => compiled.push(ClauseForCompiled {
                    var,
                    over,
                    ifs: Vec::new(),
                    local_names_to_indices: Default::default(),
                }),
                Clause::If(cond) => {
                    compiled.last_mut().unwrap().ifs.push(cond);
                }
            }
        }
        compiled
            .into_iter()
            .map(ClauseForCompiled::compile_clause)
            .collect::<Result<_, _>>()
    }
}

#[derive(Debug, Clone)]
pub enum ComprehensionCompiled {
    List(AstExpr, Vec<ClauseForCompiled>),
    Set(AstExpr, Vec<ClauseForCompiled>),
    // key, value, clauses
    Dict(AstExpr, AstExpr, Vec<ClauseForCompiled>),
}

impl ComprehensionCompiled {
    pub(crate) fn new_list(
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ComprehensionCompiled, Diagnostic> {
        let fors = ClauseForCompiled::compile_clauses(clauses)?;
        Ok(ComprehensionCompiled::List(
            Expr::transform_locals_to_slots(expr, &fors.last().unwrap().local_names_to_indices),
            fors,
        ))
    }

    pub(crate) fn new_set(
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ComprehensionCompiled, Diagnostic> {
        let fors = ClauseForCompiled::compile_clauses(clauses)?;
        Ok(ComprehensionCompiled::Set(
            Expr::transform_locals_to_slots(expr, &fors.last().unwrap().local_names_to_indices),
            fors,
        ))
    }

    pub(crate) fn new_dict(
        key: AstExpr,
        value: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ComprehensionCompiled, Diagnostic> {
        let fors = ClauseForCompiled::compile_clauses(clauses)?;
        Ok(ComprehensionCompiled::Dict(
            Expr::transform_locals_to_slots(key, &fors.last().unwrap().local_names_to_indices),
            Expr::transform_locals_to_slots(value, &fors.last().unwrap().local_names_to_indices),
            fors,
        ))
    }

    pub(crate) fn to_raw(&self) -> Expr {
        match self {
            ComprehensionCompiled::List(expr, fors) => {
                Expr::ListComprehension(expr.clone(), ClauseForCompiled::compiled_to_raw(&fors))
            }
            ComprehensionCompiled::Set(expr, fors) => {
                Expr::SetComprehension(expr.clone(), ClauseForCompiled::compiled_to_raw(&fors))
            }
            ComprehensionCompiled::Dict(key, value, fors) => Expr::DictComprehension(
                (key.clone(), value.clone()),
                ClauseForCompiled::compiled_to_raw(&fors),
            ),
        }
    }

    pub(crate) fn eval(&self, expr_span: Span, context: &EvaluationContext) -> EvalResult {
        match self {
            ComprehensionCompiled::List(expr, fors) => {
                let mut values = Vec::new();
                eval_one_dimensional_comprehension(&expr, &fors, context, &mut values)?;
                Ok(Value::from(values))
            }
            ComprehensionCompiled::Set(expr, fors) => {
                let mut values = Vec::new();
                eval_one_dimensional_comprehension(&expr, &fors, context, &mut values)?;
                make_set(values, context, expr_span)
            }
            ComprehensionCompiled::Dict(key, value, fors) => {
                let mut r = Dictionary::new_typed();
                let tuple = Box::new(Spanned {
                    span: key.span.merge(value.span),
                    // TODO: clone might be expensive
                    node: Expr::Tuple(vec![key.clone(), value.clone()]),
                });
                let mut pairs = Vec::new();
                eval_one_dimensional_comprehension(&tuple, &fors, context, &mut pairs)?;
                for e in pairs {
                    let k = t(e.at(Value::from(0)), &tuple)?;
                    let v = t(e.at(Value::from(1)), &tuple)?;
                    t(r.set_at(k, v), &tuple)?;
                }
                Ok(Value::new(r))
            }
        }
    }
}

fn eval_one_dimensional_comprehension<'a>(
    e: &AstExpr,
    clauses: &[ClauseForCompiled],
    context: &EvaluationContext,
    collect: &mut Vec<Value>,
) -> Result<(), EvalException> {
    if let Some((c, tl)) = clauses.split_first() {
        let mut iterable = eval_expr(&c.over, context)?;
        iterable.freeze_for_iteration();
        'f: for i in &t(iterable.iter(), &c.over.span)? {
            let context = context.child(&c.local_names_to_indices);
            set_expr(&c.var, &context, i)?;

            for ifc in &c.ifs {
                if !eval_expr(ifc, &context)?.to_bool() {
                    continue 'f;
                }
            }

            eval_one_dimensional_comprehension(e, tl, &context, collect)?;
        }

        iterable.unfreeze_for_iteration();
    } else {
        collect.push(eval_expr(e, &context)?);
    }
    Ok(())
}
