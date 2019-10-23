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

use crate::eval::eval_expr;
use crate::eval::set_expr;
use crate::eval::t;
use crate::eval::EvalException;
use crate::eval::EvaluationContext;
use crate::syntax::ast::AstClause;
use crate::syntax::ast::Clause;

pub(crate) fn eval_one_dimensional_comprehension<
    F: FnMut(&EvaluationContext) -> Result<(), EvalException>,
>(
    expr: &mut F,
    clauses: &[AstClause],
    context: &EvaluationContext,
) -> Result<(), EvalException> {
    if let Some((first, tl)) = clauses.split_first() {
        match &first.node {
            Clause::If(ref cond) => {
                if !eval_expr(cond, context)?.to_bool() {
                    return Ok(());
                }
                eval_one_dimensional_comprehension(expr, tl, context)
            }
            Clause::For(ref var, ref iter) => {
                let mut iterable = eval_expr(iter, context)?;
                iterable.freeze_for_iteration();
                for item in &t(iterable.iter(), iter)? {
                    set_expr(var, context, item)?;

                    eval_one_dimensional_comprehension(expr, tl, context)?;
                }

                iterable.unfreeze_for_iteration();
                Ok(())
            }
        }
    } else {
        expr(context)
    }
}
