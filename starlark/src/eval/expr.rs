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

//! Interpreter-ready expr

use crate::eval::compiler::GlobalCompiler;
use crate::eval::compiler::LocalCompiler;
use crate::eval::compiler::LocalOrGlobalCompiler;
use crate::eval::locals::Locals;
use crate::eval::locals::LocalsQuery;
use crate::syntax::ast::AssignTargetExpr;
use crate::syntax::ast::AstAssignTargetExpr;
use crate::syntax::ast::AstAugmentedAssignTargetExpr;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignTargetExpr;
use crate::syntax::ast::BinOp;
use crate::syntax::ast::Expr;
use crate::values::Value;
use codemap::Spanned;
use codemap_diagnostic::Diagnostic;

/// After syntax check each variable is resolved to either global or slot
#[derive(Debug, Clone)]
pub(crate) enum GlobalOrSlot {
    Global(String),
    Slot(usize, String),
}
pub(crate) type AstGlobalOrSlot = Spanned<GlobalOrSlot>;

#[derive(Debug, Clone)]
pub(crate) enum AssignTargetExprCompiled {
    Name(AstGlobalOrSlot),
    Dot(AstExprCompiled, AstString),
    ArrayIndirection(AstExprCompiled, AstExprCompiled),
    Subtargets(Vec<AstAssignTargetExprCompiled>),
}
pub(crate) type AstAssignTargetExprCompiled = Spanned<AssignTargetExprCompiled>;

#[derive(Debug, Clone)]
pub(crate) enum AugmentedAssignTargetExprCompiled {
    // there's no augmented assignment for globals
    Slot(usize, AstString),
    Dot(AstExprCompiled, AstString),
    ArrayIndirection(AstExprCompiled, AstExprCompiled),
}
pub(crate) type AstAugmentedAssignTargetExprCompiled = Spanned<AugmentedAssignTargetExprCompiled>;

#[doc(hidden)]
#[derive(Debug, Clone)]
pub(crate) enum ClauseCompiled {
    For(AstAssignTargetExprCompiled, AstExprCompiled),
    If(AstExprCompiled),
}
pub(crate) type AstClauseCompiled = Spanned<ClauseCompiled>;

/// Interperter-ready version of [`Expr`](crate::syntax::ast::Expr)
#[derive(Debug, Clone)]
pub(crate) enum ExprCompiled {
    Tuple(Vec<AstExprCompiled>),
    Dot(AstExprCompiled, AstString),
    Call(
        AstExprCompiled,
        Vec<AstExprCompiled>,
        Vec<(AstString, AstExprCompiled)>,
        Option<AstExprCompiled>,
        Option<AstExprCompiled>,
    ),
    ArrayIndirection(AstExprCompiled, AstExprCompiled),
    Slice(
        AstExprCompiled,
        Option<AstExprCompiled>,
        Option<AstExprCompiled>,
        Option<AstExprCompiled>,
    ),
    Name(AstGlobalOrSlot),
    Value(Value),
    Not(AstExprCompiled),
    Minus(AstExprCompiled),
    Plus(AstExprCompiled),
    And(AstExprCompiled, AstExprCompiled),
    Or(AstExprCompiled, AstExprCompiled),
    Op(BinOp, AstExprCompiled, AstExprCompiled),
    If(AstExprCompiled, AstExprCompiled, AstExprCompiled), // Order: condition, v1, v2 <=> v1 if condition else v2
    List(Vec<AstExprCompiled>),
    Set(Vec<AstExprCompiled>),
    Dict(Vec<(AstExprCompiled, AstExprCompiled)>),
    ListComprehension(AstExprCompiled, Vec<AstClauseCompiled>),
    SetComprehension(AstExprCompiled, Vec<AstClauseCompiled>),
    DictComprehension((AstExprCompiled, AstExprCompiled), Vec<AstClauseCompiled>),
    /// Creates a local scope for evaluation of subexpression in global scope.
    /// Used for evaluate comprehensions in global scope.
    Local(AstExprCompiled, Locals),
}

#[doc(hidden)]
pub(crate) type AstExprCompiled = Box<Spanned<ExprCompiled>>;

impl ExprCompiled {
    pub(crate) fn compile<C: LocalOrGlobalCompiler>(
        expr: AstExpr,
        compiler: &mut C,
    ) -> Result<AstExprCompiled, Diagnostic> {
        Ok(Box::new(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Tuple(args) => ExprCompiled::Tuple(
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::List(args) => ExprCompiled::List(
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Set(args) => ExprCompiled::Set(
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Dict(args) => ExprCompiled::Dict(
                    args.into_iter()
                        .map(|(k, v)| {
                            Ok((Self::compile(k, compiler)?, Self::compile(v, compiler)?))
                        })
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Identifier(ident) => ExprCompiled::Name(Spanned {
                    span: ident.span,
                    node: compiler.ident(ident),
                }),
                Expr::Dot(object, field) => {
                    ExprCompiled::Dot(Self::compile(object, compiler)?, field)
                }
                Expr::ArrayIndirection(array, index) => ExprCompiled::ArrayIndirection(
                    Self::compile(array, compiler)?,
                    Self::compile(index, compiler)?,
                ),
                Expr::Call(f, args, kwargs, star, star_star) => ExprCompiled::Call(
                    Self::compile(f, compiler)?,
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                    kwargs
                        .into_iter()
                        .map(|(k, v)| Ok((k, Self::compile(v, compiler)?)))
                        .collect::<Result<_, _>>()?,
                    star.map(|e| Self::compile(e, compiler)).transpose()?,
                    star_star.map(|e| Self::compile(e, compiler)).transpose()?,
                ),
                Expr::Slice(array, a, b, c) => ExprCompiled::Slice(
                    Self::compile(array, compiler)?,
                    a.map(|e| Self::compile(e, compiler)).transpose()?,
                    b.map(|e| Self::compile(e, compiler)).transpose()?,
                    c.map(|e| Self::compile(e, compiler)).transpose()?,
                ),
                Expr::IntLiteral(i) => ExprCompiled::Value(Value::from(i.node)),
                Expr::StringLiteral(s) => ExprCompiled::Value(Value::from(s.node)),
                Expr::Not(e) => ExprCompiled::Not(Self::compile(e, compiler)?),
                Expr::Plus(e) => ExprCompiled::Plus(Self::compile(e, compiler)?),
                Expr::Minus(e) => ExprCompiled::Minus(Self::compile(e, compiler)?),
                Expr::And(lhs, rhs) => {
                    ExprCompiled::And(Self::compile(lhs, compiler)?, Self::compile(rhs, compiler)?)
                }
                Expr::Or(lhs, rhs) => {
                    ExprCompiled::Or(Self::compile(lhs, compiler)?, Self::compile(rhs, compiler)?)
                }
                Expr::Op(op, lhs, rhs) => ExprCompiled::Op(
                    op,
                    Self::compile(lhs, compiler)?,
                    Self::compile(rhs, compiler)?,
                ),
                Expr::If(cond, then_expr, else_expr) => ExprCompiled::If(
                    Self::compile(cond, compiler)?,
                    Self::compile(then_expr, compiler)?,
                    Self::compile(else_expr, compiler)?,
                ),
                Expr::ListComprehension(expr, clauses) => {
                    compiler.list_comprenesion(expr.span, expr, clauses)?
                }
                Expr::SetComprehension(expr, clauses) => {
                    compiler.set_comprenesion(expr.span, expr, clauses)?
                }
                Expr::DictComprehension((key, value), clauses) => {
                    compiler.dict_comprenesion(expr.span, key, value, clauses)?
                }
            },
        }))
    }

    pub(crate) fn compile_local<'a>(
        expr: AstExpr,
        locals_query: &'a mut LocalsQuery<'a>,
    ) -> Result<AstExprCompiled, Diagnostic> {
        Self::compile(expr, &mut LocalCompiler::new(locals_query))
    }

    pub(crate) fn compile_global(expr: AstExpr) -> Result<AstExprCompiled, Diagnostic> {
        Self::compile(expr, &mut GlobalCompiler)
    }
}

impl AssignTargetExprCompiled {
    pub(crate) fn compile<C: LocalOrGlobalCompiler>(
        expr: AstAssignTargetExpr,
        compiler: &mut C,
    ) -> Result<AstAssignTargetExprCompiled, Diagnostic> {
        Ok(Spanned {
            span: expr.span,
            node: match expr.node {
                AssignTargetExpr::Identifier(a) => {
                    AssignTargetExprCompiled::Name(compiler.ast_ident(a))
                }
                AssignTargetExpr::ArrayIndirection(array, index) => {
                    AssignTargetExprCompiled::ArrayIndirection(
                        ExprCompiled::compile(array, compiler)?,
                        ExprCompiled::compile(index, compiler)?,
                    )
                }
                AssignTargetExpr::Dot(object, field) => {
                    AssignTargetExprCompiled::Dot(ExprCompiled::compile(object, compiler)?, field)
                }
                AssignTargetExpr::Subtargets(subtargets) => AssignTargetExprCompiled::Subtargets(
                    subtargets
                        .into_iter()
                        .map(|t| AssignTargetExprCompiled::compile(t, compiler))
                        .collect::<Result<_, _>>()?,
                ),
            },
        })
    }
}

impl AugmentedAssignTargetExprCompiled {
    pub(crate) fn compile_impl<C: LocalOrGlobalCompiler>(
        expr: AstAugmentedAssignTargetExpr,
        compiler: &mut C,
    ) -> Result<AstAugmentedAssignTargetExprCompiled, Diagnostic> {
        Ok(Spanned {
            span: expr.span,
            node: match expr.node {
                AugmentedAssignTargetExpr::Identifier(a) => {
                    let span = a.span;
                    match compiler.ident(a) {
                        GlobalOrSlot::Global(..) => {
                            unreachable!("must be filtered out at parse level")
                        }
                        GlobalOrSlot::Slot(slot, ident) => AugmentedAssignTargetExprCompiled::Slot(
                            slot,
                            Spanned { span, node: ident },
                        ),
                    }
                }
                AugmentedAssignTargetExpr::ArrayIndirection(array, index) => {
                    AugmentedAssignTargetExprCompiled::ArrayIndirection(
                        ExprCompiled::compile(array, compiler)?,
                        ExprCompiled::compile(index, compiler)?,
                    )
                }
                AugmentedAssignTargetExpr::Dot(object, field) => {
                    AugmentedAssignTargetExprCompiled::Dot(
                        ExprCompiled::compile(object, compiler)?,
                        field,
                    )
                }
            },
        })
    }
}
