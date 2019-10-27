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

use crate::eval::compiler::GlobalCompiler;
use crate::eval::compiler::LocalCompiler;
use crate::eval::def::DefCompiled;
use crate::eval::expr::AssignTargetExprCompiled;
use crate::eval::expr::AstAssignTargetExprCompiled;
use crate::eval::expr::AstAugmentedAssignTargetExprCompiled;
use crate::eval::expr::AstExprCompiled;
use crate::eval::expr::AugmentedAssignTargetExprCompiled;
use crate::eval::expr::ExprCompiled;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignOp;
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
    Return(Option<AstExprCompiled>),
    Expression(AstExprCompiled),
    Assign(AstAssignTargetExprCompiled, AstExprCompiled),
    AugmentedAssign(
        AstAugmentedAssignTargetExprCompiled,
        AugmentedAssignOp,
        AstExprCompiled,
    ),
    IfElse(AstExprCompiled, BlockCompiled, BlockCompiled),
    For(AstAssignTargetExprCompiled, AstExprCompiled, BlockCompiled),
    Def(DefCompiled),
    Load(AstString, Vec<(AstString, AstString)>),
}

#[derive(Debug, Clone)]
pub(crate) struct BlockCompiled(pub(crate) Vec<AstStatementCompiled>);

impl BlockCompiled {
    fn compile_local_stmts(
        stmts: Vec<AstStatement>,
        compiler: &mut LocalCompiler,
    ) -> Result<BlockCompiled, Diagnostic> {
        let mut r = Vec::new();
        for stmt in stmts {
            r.extend(Self::compile_local(stmt, compiler)?.0);
        }
        Ok(BlockCompiled(r))
    }

    pub(crate) fn compile_local(
        stmt: AstStatement,
        compiler: &mut LocalCompiler,
    ) -> Result<BlockCompiled, Diagnostic> {
        Ok(BlockCompiled(vec![Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::Def(..) => unreachable!(),
                Statement::For(var, over, body) => {
                    let over = ExprCompiled::compile(over, compiler)?;
                    StatementCompiled::For(
                        AssignTargetExprCompiled::compile(var, compiler)?,
                        over,
                        BlockCompiled::compile_local(body, compiler)?,
                    )
                }
                Statement::Return(Some(expr)) => {
                    StatementCompiled::Return(Some(ExprCompiled::compile(expr, compiler)?))
                }
                Statement::Return(None) => StatementCompiled::Return(None),
                Statement::If(cond, then_block) => StatementCompiled::IfElse(
                    ExprCompiled::compile(cond, compiler)?,
                    BlockCompiled::compile_local(then_block, compiler)?,
                    BlockCompiled(Vec::new()),
                ),
                Statement::IfElse(cond, then_block, else_block) => StatementCompiled::IfElse(
                    ExprCompiled::compile(cond, compiler)?,
                    BlockCompiled::compile_local(then_block, compiler)?,
                    BlockCompiled::compile_local(else_block, compiler)?,
                ),
                Statement::Statements(stmts) => {
                    return BlockCompiled::compile_local_stmts(stmts, compiler)
                }
                Statement::Expression(e) => {
                    StatementCompiled::Expression(ExprCompiled::compile(e, compiler)?)
                }
                Statement::Assign(left, right) => StatementCompiled::Assign(
                    AssignTargetExprCompiled::compile(left, compiler)?,
                    ExprCompiled::compile(right, compiler)?,
                ),
                Statement::AugmentedAssign(left, op, right) => StatementCompiled::AugmentedAssign(
                    AugmentedAssignTargetExprCompiled::compile_impl(left, compiler)?,
                    op,
                    ExprCompiled::compile(right, compiler)?,
                ),
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
                    AssignTargetExprCompiled::compile(var, &mut GlobalCompiler)?,
                    ExprCompiled::compile_global(over)?,
                    BlockCompiled::compile_global(body)?,
                ),
                Statement::If(cond, then_block) => StatementCompiled::IfElse(
                    ExprCompiled::compile_global(cond)?,
                    BlockCompiled::compile_global(then_block)?,
                    BlockCompiled(Vec::new()),
                ),
                Statement::IfElse(cond, then_block, else_block) => StatementCompiled::IfElse(
                    ExprCompiled::compile_global(cond)?,
                    BlockCompiled::compile_global(then_block)?,
                    BlockCompiled::compile_global(else_block)?,
                ),
                Statement::Statements(stmts) => return BlockCompiled::compile_global_stmts(stmts),
                Statement::Expression(expr) => {
                    StatementCompiled::Expression(ExprCompiled::compile_global(expr)?)
                }
                Statement::Return(Some(expr)) => {
                    StatementCompiled::Return(Some(ExprCompiled::compile_global(expr)?))
                }
                Statement::Assign(target, source) => StatementCompiled::Assign(
                    AssignTargetExprCompiled::compile(target, &mut GlobalCompiler)?,
                    ExprCompiled::compile_global(source)?,
                ),
                Statement::AugmentedAssign(target, op, source) => {
                    StatementCompiled::AugmentedAssign(
                        AugmentedAssignTargetExprCompiled::compile_impl(
                            target,
                            &mut GlobalCompiler,
                        )?,
                        op,
                        ExprCompiled::compile_global(source)?,
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
