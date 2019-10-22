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
use crate::eval::stmt::{AstStatementCompiled, StatementCompiled};
use crate::eval::{
    eval_stmt, EvalException, EvaluationContext, EvaluationContextEnvironment, IndexedLocals,
};
use crate::syntax::ast::AssignTargetExpr;
use crate::syntax::ast::AstParameter;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignTargetExpr;
use crate::syntax::ast::Expr;
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
use std::collections::HashMap;
use std::convert::TryInto;
use std::fmt;
use std::iter;
use std::sync::{Arc, Mutex};

/// `def` AST with post-processing suitable for faster excecution
#[doc(hidden)]
#[derive(Debug, Clone)]
pub struct DefCompiled {
    pub(crate) name: AstString,
    pub(crate) params: Vec<AstParameter>,
    pub(crate) suite: AstStatementCompiled,
    local_names_to_indices: HashMap<String, usize>,
}

impl DefCompiled {
    pub fn new(
        name: AstString,
        params: Vec<AstParameter>,
        suite: AstStatement,
    ) -> Result<DefCompiled, Diagnostic> {
        let mut local_names_to_indices = HashMap::new();

        for p in &params {
            let len = local_names_to_indices.len();
            local_names_to_indices
                .entry(p.name().to_owned())
                .or_insert(len);
        }

        DefCompiled::collect_locals(&suite, &mut local_names_to_indices);

        let suite = DefCompiled::transform_locals(suite, &local_names_to_indices);

        let suite = StatementCompiled::compile(suite)?;

        Ok(DefCompiled {
            name,
            params,
            suite,
            local_names_to_indices,
        })
    }

    fn collect_locals(stmt: &AstStatement, local_names_to_indices: &mut HashMap<String, usize>) {
        match stmt.node {
            Statement::Assign(ref dest, ..) => {
                AssignTargetExpr::collect_locals_from_assign_expr(dest, local_names_to_indices);
            }
            Statement::AugmentedAssign(ref dest, ..) => {
                AugmentedAssignTargetExpr::collect_locals_from_assign_expr(
                    dest,
                    local_names_to_indices,
                );
            }
            Statement::For(ref dest, _, ref body) => {
                AssignTargetExpr::collect_locals_from_assign_expr(dest, local_names_to_indices);
                DefCompiled::collect_locals(body, local_names_to_indices);
            }
            Statement::Statements(ref stmts) => {
                for stmt in stmts {
                    DefCompiled::collect_locals(stmt, local_names_to_indices);
                }
            }
            Statement::If(_, ref then_block) => {
                DefCompiled::collect_locals(then_block, local_names_to_indices);
            }
            Statement::IfElse(_, ref then_block, ref else_block) => {
                DefCompiled::collect_locals(then_block, local_names_to_indices);
                DefCompiled::collect_locals(else_block, local_names_to_indices);
            }
            Statement::Break
            | Statement::Continue
            | Statement::Pass
            | Statement::Return(..)
            | Statement::Expression(..) => {}
            Statement::Load(..) | Statement::Def(..) => unreachable!(),
        }
    }

    /// Transform statement replacing local variables access by name with access by index
    fn transform_locals(stmts: AstStatement, locals: &HashMap<String, usize>) -> AstStatement {
        Box::new(Spanned {
            span: stmts.span,
            node: match stmts.node {
                Statement::Assign(left, right) => Statement::Assign(
                    AssignTargetExpr::transform_locals_to_slots(left, locals),
                    Expr::transform_locals_to_slots(right, locals),
                ),
                Statement::AugmentedAssign(target, op, rhs) => Statement::AugmentedAssign(
                    AugmentedAssignTargetExpr::transform_locals_to_slots(target, locals),
                    op,
                    Expr::transform_locals_to_slots(rhs, locals),
                ),
                Statement::For(var, collection, body) => Statement::For(
                    AssignTargetExpr::transform_locals_to_slots(var, locals),
                    Expr::transform_locals_to_slots(collection, locals),
                    DefCompiled::transform_locals(body, locals),
                ),
                Statement::Statements(stmts) => Statement::Statements(
                    stmts
                        .into_iter()
                        .map(|stmt| DefCompiled::transform_locals(stmt, locals))
                        .collect(),
                ),
                Statement::If(cond, then_block) => Statement::If(
                    Expr::transform_locals_to_slots(cond, locals),
                    DefCompiled::transform_locals(then_block, locals),
                ),
                Statement::IfElse(cond, then_block, else_block) => Statement::IfElse(
                    Expr::transform_locals_to_slots(cond, locals),
                    DefCompiled::transform_locals(then_block, locals),
                    DefCompiled::transform_locals(else_block, locals),
                ),
                s @ Statement::Break | s @ Statement::Continue | s @ Statement::Pass => s,
                Statement::Def(..) | Statement::Load(..) => unreachable!(),
                Statement::Expression(expr) => {
                    Statement::Expression(Expr::transform_locals_to_slots(expr, locals))
                }
                Statement::Return(expr) => Statement::Return(
                    expr.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                ),
            },
        })
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
            env: EvaluationContextEnvironment::Function(
                self.captured_env.clone(),
                IndexedLocals::new(&self.stmt.local_names_to_indices),
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

        for (s, positional_only) in self.signature.iter() {
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
            if let Err(x) = ctx.env.set(name, v) {
                return Err(x.into());
            }
        }

        parser.check_no_more_args()?;

        match eval_stmt(&self.stmt.suite, &mut ctx) {
            Err(EvalException::Return(_s, ret)) => Ok(ret),
            Err(x) => Err(ValueError::DiagnosedError(x.into())),
            Ok(..) => Ok(Value::new(NoneType::None)),
        }
    }
}
