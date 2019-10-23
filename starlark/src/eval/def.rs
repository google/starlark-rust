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

//! Implementation of `def`.

use crate::environment::{Environment, TypeValues};
use crate::eval::call_stack::CallStack;
use crate::eval::compiler::LocalCompiler;
use crate::eval::eval_block;
use crate::eval::expr::AstExprCompiled;
use crate::eval::expr::ExprCompiled;
use crate::eval::locals::Locals;
use crate::eval::locals::LocalsBuilder;
use crate::eval::locals::LocalsQuery;
use crate::eval::stmt::BlockCompiled;
use crate::eval::EvalException;
use crate::eval::EvaluationContext;
use crate::eval::EvaluationContextEnvironment;
use crate::eval::IndexedLocals;
use crate::syntax::ast::AssignTargetExpr;
use crate::syntax::ast::AstParameter;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignTargetExpr;
use crate::syntax::ast::Expr;
use crate::syntax::ast::Parameter;
use crate::syntax::ast::Statement;
use crate::values::error::ValueError;
use crate::values::function::FunctionParameter;
use crate::values::function::FunctionSignature;
use crate::values::function::FunctionType;
use crate::values::function::StrOrRepr;
use crate::values::none::NoneType;
use crate::values::{function, Immutable, TypedValue, Value, ValueResult};
use codemap::{CodeMap, Spanned};
use codemap_diagnostic::Diagnostic;
use linked_hash_map::LinkedHashMap;
use std::convert::TryInto;
use std::fmt;
use std::iter;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
pub(crate) enum ParameterCompiled {
    Normal(AstString),
    WithDefaultValue(AstString, AstExprCompiled),
    Args(AstString),
    KWArgs(AstString),
}
pub(crate) type AstParameterCompiled = Spanned<ParameterCompiled>;

impl ParameterCompiled {
    fn compile(param: AstParameter) -> Result<AstParameterCompiled, Diagnostic> {
        Ok(Spanned {
            span: param.span,
            node: match param.node {
                Parameter::Normal(n) => ParameterCompiled::Normal(n),
                Parameter::WithDefaultValue(n, d) => {
                    ParameterCompiled::WithDefaultValue(n, ExprCompiled::compile_global(d)?)
                }
                Parameter::Args(args) => ParameterCompiled::Args(args),
                Parameter::KWArgs(args) => ParameterCompiled::KWArgs(args),
            },
        })
    }
}

/// `def` AST with post-processing suitable for faster excecution
#[doc(hidden)]
#[derive(Debug, Clone)]
pub struct DefCompiled {
    pub(crate) name: AstString,
    pub(crate) params: Vec<AstParameterCompiled>,
    pub(crate) suite: BlockCompiled,
    locals: Locals,
}

impl DefCompiled {
    pub fn new(
        name: AstString,
        params: Vec<AstParameter>,
        suite: AstStatement,
    ) -> Result<DefCompiled, Diagnostic> {
        let mut locals_builder = LocalsBuilder::default();

        for p in &params {
            locals_builder.register_local(p.name());
        }

        let params = params
            .into_iter()
            .map(ParameterCompiled::compile)
            .collect::<Result<_, _>>()?;

        DefCompiled::collect_locals(&suite, &mut locals_builder);

        let locals = locals_builder.build();

        let mut locals_query = LocalsQuery::new(&locals);

        let mut local_compiler = LocalCompiler::new(&mut locals_query);

        let suite = BlockCompiled::compile_local(suite, &mut local_compiler)?;

        Ok(DefCompiled {
            name,
            params,
            suite,
            locals,
        })
    }

    fn collect_locals(stmt: &AstStatement, locals_builder: &mut LocalsBuilder) {
        match stmt.node {
            Statement::Assign(ref dest, ref source) => {
                AssignTargetExpr::collect_locals_from_assign_expr(dest, locals_builder);
                Expr::collect_locals(source, locals_builder);
            }
            Statement::AugmentedAssign(ref dest, _op, ref source) => {
                AugmentedAssignTargetExpr::collect_locals_from_assign_expr(dest, locals_builder);
                Expr::collect_locals(source, locals_builder);
            }
            Statement::For(ref dest, ref iter, ref body) => {
                AssignTargetExpr::collect_locals_from_assign_expr(dest, locals_builder);
                Expr::collect_locals(iter, locals_builder);
                DefCompiled::collect_locals(body, locals_builder);
            }
            Statement::Statements(ref stmts) => {
                for stmt in stmts {
                    DefCompiled::collect_locals(stmt, locals_builder);
                }
            }
            Statement::If(ref cond, ref then_block) => {
                Expr::collect_locals(cond, locals_builder);
                DefCompiled::collect_locals(then_block, locals_builder);
            }
            Statement::IfElse(ref cond, ref then_block, ref else_block) => {
                Expr::collect_locals(cond, locals_builder);
                DefCompiled::collect_locals(then_block, locals_builder);
                DefCompiled::collect_locals(else_block, locals_builder);
            }
            Statement::Return(ref expr) => {
                if let Some(expr) = expr {
                    Expr::collect_locals(expr, locals_builder);
                }
            }
            Statement::Expression(ref expr) => {
                Expr::collect_locals(expr, locals_builder);
            }
            Statement::Break | Statement::Continue | Statement::Pass => {}
            Statement::Load(..) | Statement::Def(..) => unreachable!(),
        }
    }
}

/// Starlark function internal representation and implementation of [`TypedValue`].
pub(crate) struct Def {
    signature: FunctionSignature,
    function_type: FunctionType,
    captured_env: Environment,
    map: Arc<Mutex<CodeMap>>,
    stmt: DefCompiled,
}

impl Def {
    pub fn new(
        module: String,
        signature: FunctionSignature,
        stmt: DefCompiled,
        map: Arc<Mutex<CodeMap>>,
        env: Environment,
    ) -> Value {
        // This can be implemented by delegating to `Function::new`,
        // but having a separate type allows slight more efficient implementation
        // and optimizations in the future.
        Value::new(Def {
            function_type: FunctionType::Def(stmt.name.node.clone(), module),
            signature,
            stmt,
            captured_env: env,
            map,
        })
    }
}

impl TypedValue for Def {
    type Holder = Immutable<Def>;

    const TYPE: &'static str = "function";

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(iter::empty())
    }

    fn to_str_impl(&self, buf: &mut String) -> fmt::Result {
        function::str_impl(buf, &self.function_type, &self.signature, StrOrRepr::Str)
    }

    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        function::str_impl(buf, &self.function_type, &self.signature, StrOrRepr::Repr)
    }

    fn call(
        &self,
        call_stack: &CallStack,
        type_values: TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        // argument binding
        let mut ctx = EvaluationContext {
            call_stack: call_stack.to_owned(),
            env: EvaluationContextEnvironment::Local(
                self.captured_env.clone(),
                IndexedLocals::new(&self.stmt.locals),
            ),
            type_values,
            map: self.map.clone(),
        };

        let mut parser = function::ParameterParser::new(
            &self.signature,
            &self.function_type,
            positional,
            named,
            args,
            kwargs,
        )?;

        for (i, (s, positional_only)) in self.signature.iter().enumerate() {
            let (name, v) = match s {
                FunctionParameter::Normal(ref name) => {
                    (name, parser.next_normal(name, positional_only)?)
                }
                FunctionParameter::WithDefaultValue(ref name, ref default_value) => (
                    name,
                    parser.next_with_default_value(name, positional_only, default_value),
                ),
                FunctionParameter::ArgsArray(ref name) => (name, parser.next_args_array().into()),
                FunctionParameter::KWArgsDict(ref name) => {
                    (name, parser.next_kwargs_dict().try_into().unwrap())
                }
                FunctionParameter::Optional(..) => {
                    unreachable!("optional parameters only exist in native functions")
                }
            };

            // tricky part: we know that we assign locals for function parameters
            // sequentially starting from 0
            if cfg!(debug_assertions) {
                assert_eq!(i, ctx.env.top_level_local_to_slot(name));
            }
            ctx.env.set_slot(i, name, v);
        }

        parser.check_no_more_args()?;

        match eval_block(&self.stmt.suite, &mut ctx) {
            Err(EvalException::Return(_s, ret)) => Ok(ret),
            Err(x) => Err(ValueError::DiagnosedError(x.into())),
            Ok(..) => Ok(Value::new(NoneType::None)),
        }
    }
}
