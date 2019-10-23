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
use crate::syntax::ast::AstAugmentedAssignTargetExpr;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignOp;
use crate::syntax::ast::Statement;
use crate::syntax::ast::{AstAssignTargetExpr, AugmentedAssignTargetExpr, Expr};
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
    fn compile_local_stmts(stmts: Vec<AstStatement>) -> Result<BlockCompiled, Diagnostic> {
        let mut r = Vec::new();
        for stmt in stmts {
            r.extend(Self::compile_local(stmt)?.0);
        }
        Ok(BlockCompiled(r))
    }

    pub(crate) fn compile_local(stmt: AstStatement) -> Result<BlockCompiled, Diagnostic> {
        Ok(BlockCompiled(vec![Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::Def(..) => unreachable!(),
                Statement::For(var, over, body) => {
                    StatementCompiled::For(var, over, BlockCompiled::compile_local(body)?)
                }
                Statement::Return(expr) => StatementCompiled::Return(expr),
                Statement::If(cond, then_block) => StatementCompiled::IfElse(
                    cond,
                    BlockCompiled::compile_local(then_block)?,
                    BlockCompiled(Vec::new()),
                ),
                Statement::IfElse(conf, then_block, else_block) => StatementCompiled::IfElse(
                    conf,
                    BlockCompiled::compile_local(then_block)?,
                    BlockCompiled::compile_local(else_block)?,
                ),
                Statement::Statements(stmts) => return BlockCompiled::compile_local_stmts(stmts),
                Statement::Expression(e) => StatementCompiled::Expression(e),
                Statement::Assign(left, right) => StatementCompiled::Assign(left, right),
                Statement::AugmentedAssign(left, op, right) => {
                    StatementCompiled::AugmentedAssign(left, op, right)
                }
                Statement::Load(module, args) => StatementCompiled::Load(module, args),
                Statement::Pass => return Ok(BlockCompiled(Vec::new())),
                Statement::Break => StatementCompiled::Break,
                Statement::Continue => StatementCompiled::Continue,
            },
        }]))
    }

    fn compile_global_stmts(stmts: Vec<AstStatement>) -> Result<BlockCompiled, Diagnostic> {
        let mut r = Vec::new();
        for stmt in stmts {
            r.extend(Self::compile_global(stmt)?.0);
        }
        Ok(BlockCompiled(r))
    }

    pub(crate) fn compile_global(stmt: AstStatement) -> Result<BlockCompiled, Diagnostic> {
        Ok(BlockCompiled(vec![Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::Def(name, params, suite) => {
                    StatementCompiled::Def(DefCompiled::new(name, params, suite)?)
                }
                Statement::For(var, over, body) => StatementCompiled::For(
                    var,
                    Expr::compile_global(over)?,
                    BlockCompiled::compile_global(body)?,
                ),
                Statement::If(cond, then_block) => StatementCompiled::IfElse(
                    Expr::compile_global(cond)?,
                    BlockCompiled::compile_global(then_block)?,
                    BlockCompiled(Vec::new()),
                ),
                Statement::IfElse(cond, then_block, else_block) => StatementCompiled::IfElse(
                    Expr::compile_global(cond)?,
                    BlockCompiled::compile_global(then_block)?,
                    BlockCompiled::compile_global(else_block)?,
                ),
                Statement::Statements(stmts) => return BlockCompiled::compile_global_stmts(stmts),
                Statement::Expression(expr) => {
                    StatementCompiled::Expression(Expr::compile_global(expr)?)
                }
                Statement::Return(Some(expr)) => {
                    StatementCompiled::Return(Some(Expr::compile_global(expr)?))
                }
                Statement::Assign(target, source) => {
                    StatementCompiled::Assign(target, Expr::compile_global(source)?)
                }
                Statement::AugmentedAssign(target, op, source) => {
                    StatementCompiled::AugmentedAssign(
                        AugmentedAssignTargetExpr::compile_global(target)?,
                        op,
                        Expr::compile_global(source)?,
                    )
                }
                Statement::Load(path, map) => StatementCompiled::Load(path, map),
                Statement::Pass => return Ok(BlockCompiled(Vec::new())),
                Statement::Break => StatementCompiled::Break,
                Statement::Continue => StatementCompiled::Continue,
                Statement::Return(None) => StatementCompiled::Return(None),
            },
        }]))
    }
}
