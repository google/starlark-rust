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
pub(crate) type AstStatementCompiled = Spanned<StatementCompiled>;

/// Interperter-ready version of [`Statement`](crate::syntax::ast::Statement)
#[derive(Debug, Clone)]
pub(crate) enum StatementCompiled {
    Break,
    Continue,
    Return(Option<AstExpr>),
    Expression(AstExpr),
    Assign(AstAssignTargetExpr, AstExpr),
    AugmentedAssign(AstAugmentedAssignTargetExpr, AugmentedAssignOp, AstExpr),
    IfElse(AstExpr, BlockCompiled, BlockCompiled),
    For(AstAssignTargetExpr, AstExpr, BlockCompiled),
    Def(DefCompiled),
    Load(AstString, Vec<(AstString, AstString)>),
}

#[derive(Debug, Clone)]
pub struct BlockCompiled(pub(crate) Vec<AstStatementCompiled>);

impl BlockCompiled {
    fn compile_stmts(stmts: Vec<AstStatement>) -> Result<BlockCompiled, Diagnostic> {
        let mut r = Vec::new();
        for stmt in stmts {
            r.extend(Self::compile_stmt(stmt)?.0);
        }
        Ok(BlockCompiled(r))
    }

    pub(crate) fn compile_stmt(stmt: AstStatement) -> Result<BlockCompiled, Diagnostic> {
        Ok(BlockCompiled(vec![Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::Def(name, params, suite) => {
                    StatementCompiled::Def(DefCompiled::new(name, params, suite)?)
                }
                Statement::For(var, over, body) => StatementCompiled::For(
                    AssignTargetExpr::compile(var)?,
                    Expr::compile(over)?,
                    BlockCompiled::compile_stmt(body)?,
                ),
                Statement::Return(expr) => {
                    StatementCompiled::Return(expr.map(Expr::compile).transpose()?)
                }
                Statement::If(cond, then_block) => StatementCompiled::IfElse(
                    cond,
                    BlockCompiled::compile_stmt(then_block)?,
                    BlockCompiled(Vec::new()),
                ),
                Statement::IfElse(conf, then_block, else_block) => StatementCompiled::IfElse(
                    conf,
                    BlockCompiled::compile_stmt(then_block)?,
                    BlockCompiled::compile_stmt(else_block)?,
                ),
                Statement::Statements(stmts) => {
                    return Self::compile_stmts(stmts);
                }
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
                Statement::Pass => return Ok(BlockCompiled(Vec::new())),
                Statement::Break => StatementCompiled::Break,
                Statement::Continue => StatementCompiled::Continue,
            },
        }]))
    }
}
