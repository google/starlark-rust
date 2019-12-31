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

use crate::environment::Environment;
use crate::eval::compiler::GlobalCompiler;
use crate::eval::compiler::LocalCompiler;
use crate::eval::def::DefCompiled;
use crate::eval::expr::AssignTargetExprCompiled;
use crate::eval::expr::AstAssignTargetExprCompiled;
use crate::eval::expr::AstAugmentedAssignTargetExprCompiled;
use crate::eval::expr::AstExprCompiled;
use crate::eval::expr::AugmentedAssignTargetExprCompiled;
use crate::eval::expr::ExprCompiled;
use crate::eval::globals::Globals;
use crate::linked_hash_set::value::Set;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignOp;
use crate::syntax::ast::Statement;
use crate::syntax::fmt::comma_separated_fmt;
use crate::syntax::fmt::fmt_string_literal;
use crate::syntax::fmt::indent;
use crate::values::dict::Dictionary;
use crate::values::frozen::FrozenValue;
use crate::values::inspect::Inspectable;
use crate::values::list::List;
use crate::values::none::NoneType;
use crate::values::range::Range;
use crate::values::tuple::Tuple;
use crate::values::Value;
use codemap::Spanned;
use codemap_diagnostic::Diagnostic;
use std::fmt;

#[doc(hidden)]
pub(crate) type AstStatementCompiled = Spanned<StatementCompiled>;

/// Interperter-ready version of [`Statement`](crate::syntax::ast::Statement)
#[derive(Debug, Clone)]
pub(crate) enum StatementCompiled {
    Break,
    Continue,
    Return(AstExprCompiled),
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

#[derive(Debug, Clone, Default)]
pub(crate) struct BlockCompiled(pub(crate) Vec<AstStatementCompiled>);

impl StatementCompiled {
    fn optimize_on_freeze(
        stmt: AstStatementCompiled,
        captured_env: &Environment,
    ) -> Vec<AstStatementCompiled> {
        vec![Spanned {
            span: stmt.span,
            node: match stmt.node {
                StatementCompiled::Return(expr) => {
                    StatementCompiled::Return(ExprCompiled::optimize_on_freeze(expr, captured_env))
                }
                StatementCompiled::Expression(expr) => {
                    let expr = ExprCompiled::optimize_on_freeze(expr, captured_env);
                    StatementCompiled::Expression(expr)
                }
                StatementCompiled::IfElse(cond, then_block, else_block) => {
                    let then_block = BlockCompiled::optimize_on_freeze(then_block, captured_env);
                    let else_block = BlockCompiled::optimize_on_freeze(else_block, captured_env);
                    StatementCompiled::IfElse(cond, then_block, else_block)
                }
                StatementCompiled::For(assign, over, block) => {
                    let over = ExprCompiled::optimize_on_freeze(over, captured_env);
                    if let Ok(over) = over.node.pure() {
                        let over: Value = over.into();
                        if over.is::<List>()
                            || over.is::<Range>()
                            || over.is::<Tuple>()
                            || over.is::<Set>()
                            || over.is::<Dictionary>()
                        {
                            if !over.to_bool() {
                                return Vec::new();
                            }
                        }
                    }
                    let assign = AssignTargetExprCompiled::optimize_on_freeze(assign, captured_env);
                    let block = BlockCompiled::optimize_on_freeze(block, captured_env);
                    StatementCompiled::For(assign, over, block)
                }
                StatementCompiled::Assign(target, expr) => {
                    let target = AssignTargetExprCompiled::optimize_on_freeze(target, captured_env);
                    let expr = ExprCompiled::optimize_on_freeze(expr, captured_env);
                    StatementCompiled::Assign(target, expr)
                }
                StatementCompiled::AugmentedAssign(target, op, expr) => {
                    let target =
                        AugmentedAssignTargetExprCompiled::optimize_on_freeze(target, captured_env);
                    let expr = ExprCompiled::optimize_on_freeze(expr, captured_env);
                    StatementCompiled::AugmentedAssign(target, op, expr)
                }
                StatementCompiled::Def(..) => unreachable!(),
                StatementCompiled::Load(..) => unreachable!(),
                stmt @ StatementCompiled::Break | stmt @ StatementCompiled::Continue => stmt,
            },
        }]
    }

    fn fmt_for_test(&self, f: &mut dyn fmt::Write, tab: &str) -> fmt::Result {
        match self {
            StatementCompiled::Break => writeln!(f, "{}break", tab),
            StatementCompiled::Continue => writeln!(f, "{}continue", tab),
            StatementCompiled::Return(e) => writeln!(f, "{}return {}", tab, e.node),
            StatementCompiled::Expression(e) => writeln!(f, "{}{}", tab, e.node),
            StatementCompiled::Assign(l, r) => writeln!(f, "{}{} = {}", tab, l.node, r.node),
            StatementCompiled::AugmentedAssign(l, op, r) => {
                writeln!(f, "{}{} {} {}", tab, l.node, op, r.node)
            }
            StatementCompiled::IfElse(cond, th, el) => {
                writeln!(f, "{}if {}:", tab, cond.node)?;
                th.fmt_for_test(f, &indent(tab))?;
                writeln!(f, "{}else:", tab)?;
                el.fmt_for_test(f, &indent(tab))?;
                Ok(())
            }
            StatementCompiled::For(var, over, body) => {
                writeln!(f, "{}for {} in {}:", tab, var.node, over.node)?;
                body.fmt_for_test(f, &indent(tab))
            }
            StatementCompiled::Load(filename, v) => {
                write!(f, "{}load(", tab)?;
                fmt_string_literal(f, &filename.node)?;
                comma_separated_fmt(
                    f,
                    v,
                    |x, f| {
                        write!(f, "{} = ", x.0.node)?;
                        fmt_string_literal(f, &(x.1.node))
                    },
                    false,
                )?;
                f.write_str(")\n")
            }
            StatementCompiled::Def(def) => def.fmt_for_test(f, tab),
        }
    }
}

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
                    StatementCompiled::Return(ExprCompiled::compile(expr, compiler)?)
                }
                Statement::Return(None) => StatementCompiled::Return(Box::new(Spanned {
                    span: stmt.span,
                    node: ExprCompiled::Value(FrozenValue::from(NoneType::None)),
                })),
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

    fn compile_global_stmts(
        stmts: Vec<AstStatement>,
        globals: &mut Globals,
    ) -> Result<BlockCompiled, Diagnostic> {
        let mut r = Vec::new();
        for stmt in stmts {
            r.extend(Self::compile_global(stmt, globals)?.0);
        }
        Ok(BlockCompiled(r))
    }

    pub(crate) fn compile_global(
        stmt: AstStatement,
        globals: &mut Globals,
    ) -> Result<BlockCompiled, Diagnostic> {
        Ok(BlockCompiled(vec![Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::Def(name, params, suite) => {
                    let slot = globals.register_global(&name.node);
                    StatementCompiled::Def(DefCompiled::new(name, slot, params, suite)?)
                }
                Statement::For(var, over, body) => StatementCompiled::For(
                    AssignTargetExprCompiled::compile(var, &mut GlobalCompiler::new(globals))?,
                    ExprCompiled::compile_global(over, globals)?,
                    BlockCompiled::compile_global(body, globals)?,
                ),
                Statement::If(cond, then_block) => StatementCompiled::IfElse(
                    ExprCompiled::compile_global(cond, globals)?,
                    BlockCompiled::compile_global(then_block, globals)?,
                    BlockCompiled(Vec::new()),
                ),
                Statement::IfElse(cond, then_block, else_block) => StatementCompiled::IfElse(
                    ExprCompiled::compile_global(cond, globals)?,
                    BlockCompiled::compile_global(then_block, globals)?,
                    BlockCompiled::compile_global(else_block, globals)?,
                ),
                Statement::Statements(stmts) => {
                    return BlockCompiled::compile_global_stmts(stmts, globals)
                }
                Statement::Expression(expr) => {
                    StatementCompiled::Expression(ExprCompiled::compile_global(expr, globals)?)
                }
                Statement::Return(Some(expr)) => {
                    StatementCompiled::Return(ExprCompiled::compile_global(expr, globals)?)
                }
                Statement::Return(None) => StatementCompiled::Return(Box::new(Spanned {
                    span: stmt.span,
                    node: ExprCompiled::Value(FrozenValue::from(NoneType::None)),
                })),
                Statement::Assign(target, source) => StatementCompiled::Assign(
                    AssignTargetExprCompiled::compile(target, &mut GlobalCompiler::new(globals))?,
                    ExprCompiled::compile_global(source, globals)?,
                ),
                Statement::AugmentedAssign(target, op, source) => {
                    StatementCompiled::AugmentedAssign(
                        AugmentedAssignTargetExprCompiled::compile_impl(
                            target,
                            &mut GlobalCompiler::new(globals),
                        )?,
                        op,
                        ExprCompiled::compile_global(source, globals)?,
                    )
                }
                Statement::Load(path, map) => StatementCompiled::Load(path, map),
                Statement::Pass => return Ok(BlockCompiled(Vec::new())),
                Statement::Break => StatementCompiled::Break,
                Statement::Continue => StatementCompiled::Continue,
            },
        }]))
    }

    pub(crate) fn optimize_on_freeze(
        block: BlockCompiled,
        captured_env: &Environment,
    ) -> BlockCompiled {
        BlockCompiled(
            block
                .0
                .into_iter()
                .flat_map(|stmt| StatementCompiled::optimize_on_freeze(stmt, captured_env))
                .collect(),
        )
    }

    pub(crate) fn fmt_for_test(&self, f: &mut dyn fmt::Write, indent: &str) -> fmt::Result {
        for s in &self.0 {
            s.node.fmt_for_test(f, indent)?;
        }
        Ok(())
    }
}

impl Inspectable for BlockCompiled {
    fn inspect(&self) -> Value {
        self.0.inspect()
    }
}

impl Inspectable for StatementCompiled {
    fn inspect(&self) -> Value {
        let (name, param): (&str, Value) = match self {
            StatementCompiled::Break => ("break", Value::from(NoneType::None)),
            StatementCompiled::Continue => ("continue", Value::from(NoneType::None)),
            StatementCompiled::Return(e) => ("return", e.inspect()),
            StatementCompiled::Expression(e) => ("expression", e.inspect()),
            StatementCompiled::Assign(t, e) => ("assign", (t, e).inspect()),
            StatementCompiled::AugmentedAssign(t, op, e) => {
                ("augmented_assign", (t, format!("{:?}", op), e).inspect())
            }
            StatementCompiled::IfElse(cond, then_block, else_block) => {
                ("if_else", (cond, then_block, else_block).inspect())
            }
            StatementCompiled::For(var, over, block) => ("for", (var, over, block).inspect()),
            StatementCompiled::Def(def) => ("def", def.name.inspect()),
            StatementCompiled::Load(what, bindings) => ("load", (what, bindings).inspect()),
        };
        Value::from((Value::from(name), param))
    }
}

#[cfg(test)]
mod test {
    use crate::testutil::test_optimize_on_freeze;

    #[test]
    fn optimize_on_freeze_dummy() {
        test_optimize_on_freeze(
            "\
def f():
  return 1
",
            "\
def f():
  return 1
",
        );
    }

    #[test]
    fn prune_empty_for() {
        test_optimize_on_freeze(
            "\
L = {}

def f():
  for x in L:
    return 1
",
            "\
def f():
",
        );
    }
}
