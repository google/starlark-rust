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

//! Interpreter-ready statement

use crate::eval::def::DefCompiled;
use crate::syntax::ast::AssignTargetExpr;
use crate::syntax::ast::AstAssignTargetExpr;
use crate::syntax::ast::AstAugmentedAssignTargetExpr;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignOp;
use crate::syntax::ast::AugmentedAssignTargetExpr;
use crate::syntax::ast::Expr;
use crate::syntax::ast::Statement;
use codemap::Spanned;
use codemap_diagnostic::Diagnostic;

#[doc(hidden)]
pub type AstStatementCompiled = Box<Spanned<StatementCompiled>>;

/// Interperter-ready version of [`Statement`](crate::syntax::ast::Statement)
#[derive(Debug, Clone)]
pub enum StatementCompiled {
    Break,
    Continue,
    Pass,
    Return(Option<AstExpr>),
    Expression(AstExpr),
    Assign(AstAssignTargetExpr, AstExpr),
    AugmentedAssign(AstAugmentedAssignTargetExpr, AugmentedAssignOp, AstExpr),
    Statements(Vec<AstStatementCompiled>),
    If(AstExpr, AstStatementCompiled),
    IfElse(AstExpr, AstStatementCompiled, AstStatementCompiled),
    For(AstAssignTargetExpr, AstExpr, AstStatementCompiled),
    Def(DefCompiled),
    Load(AstString, Vec<(AstString, AstString)>),
}

impl StatementCompiled {
    pub(crate) fn compile(stmt: AstStatement) -> Result<AstStatementCompiled, Diagnostic> {
        Ok(Box::new(Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::Def(name, params, suite) => {
                    StatementCompiled::Def(DefCompiled::new(name, params, suite)?)
                }
                Statement::For(var, over, body) => StatementCompiled::For(
                    AssignTargetExpr::compile(var)?,
                    Expr::compile(over)?,
                    StatementCompiled::compile(body)?,
                ),
                Statement::Return(expr) => {
                    StatementCompiled::Return(expr.map(Expr::compile).transpose()?)
                }
                Statement::If(cond, then_block) => {
                    StatementCompiled::If(cond, StatementCompiled::compile(then_block)?)
                }
                Statement::IfElse(conf, then_block, else_block) => StatementCompiled::IfElse(
                    conf,
                    StatementCompiled::compile(then_block)?,
                    StatementCompiled::compile(else_block)?,
                ),
                Statement::Statements(stmts) => StatementCompiled::Statements(
                    stmts
                        .into_iter()
                        .map(StatementCompiled::compile)
                        .collect::<Result<_, _>>()?,
                ),
                Statement::Expression(e) => StatementCompiled::Expression(Expr::compile(e)?),
                Statement::Assign(left, right) => StatementCompiled::Assign(
                    AssignTargetExpr::compile(left)?,
                    Expr::compile(right)?,
                ),
                Statement::AugmentedAssign(left, op, right) => StatementCompiled::AugmentedAssign(
                    AugmentedAssignTargetExpr::compile(left)?,
                    op,
                    Expr::compile(right)?,
                ),
                Statement::Load(module, args) => StatementCompiled::Load(module, args),
                Statement::Pass => StatementCompiled::Pass,
                Statement::Break => StatementCompiled::Break,
                Statement::Continue => StatementCompiled::Continue,
            },
        }))
    }
}
