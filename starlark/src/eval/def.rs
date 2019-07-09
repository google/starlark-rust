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
use crate::eval::{eval_stmt, EvalException, EvaluationContext, EvaluationContextEnvironment};
use crate::syntax::ast::{AstExpr, AstStatement, Expr, Statement};
use crate::values::error::ValueError;
use crate::values::function::{FunctionParameter, FunctionType};
use crate::values::none::NoneType;
use crate::values::{function, Immutable, TypedValue, Value, ValueResult};
use codemap::CodeMap;
use linked_hash_map::LinkedHashMap;
use std::collections::HashSet;
use std::convert::TryInto;
use std::iter;
use std::sync::{Arc, Mutex};

/// Starlark function internal representation and implementation of [`TypedValue`].
pub(crate) struct Def {
    signature: Vec<FunctionParameter>,
    function_type: FunctionType,
    stmts: AstStatement,
    captured_env: Environment,
    map: Arc<Mutex<CodeMap>>,
    local_names: HashSet<String>,
}

impl Def {
    pub fn new(
        name: String,
        module: String,
        signature: Vec<FunctionParameter>,
        stmts: AstStatement,
        map: Arc<Mutex<CodeMap>>,
        env: Environment,
    ) -> Value {
        let mut local_names = HashSet::new();

        for p in &signature {
            local_names.insert(match p {
                FunctionParameter::Normal(ref n)
                | FunctionParameter::ArgsArray(ref n)
                | FunctionParameter::KWArgsDict(ref n)
                | FunctionParameter::WithDefaultValue(ref n, ..) => n.to_owned(),
                FunctionParameter::Optional(..) => unreachable!(),
            });
        }

        Def::collect_locals(&stmts, &mut local_names);

        // This can be implemented by delegating to `Function::new`,
        // but having a separate type allows slight more efficient implementation
        // and optimizations in the future.
        Value::new(Def {
            function_type: FunctionType::Def(name, module),
            signature,
            stmts,
            captured_env: env,
            map,
            local_names,
        })
    }

    fn collect_locals(stmt: &AstStatement, local_names: &mut HashSet<String>) {
        match stmt.node {
            Statement::Assign(ref dest, ..) => {
                Def::collect_locals_from_assign_expr(dest, local_names);
            }
            Statement::For(ref dest, _, ref body) => {
                Def::collect_locals_from_assign_expr(dest, local_names);
                Def::collect_locals(body, local_names);
            }
            Statement::Statements(ref stmts) => {
                for stmt in stmts {
                    Def::collect_locals(stmt, local_names);
                }
            }
            Statement::If(_, ref then_block) => {
                Def::collect_locals(then_block, local_names);
            }
            Statement::IfElse(_, ref then_block, ref else_block) => {
                Def::collect_locals(then_block, local_names);
                Def::collect_locals(else_block, local_names);
            }
            Statement::Break
            | Statement::Continue
            | Statement::Pass
            | Statement::Return(..)
            | Statement::Expression(..)
            | Statement::Load(..)
            | Statement::Def(..) => {}
        }
    }

    fn collect_locals_from_assign_expr(expr: &AstExpr, local_names: &mut HashSet<String>) {
        match expr.node {
            Expr::Tuple(ref exprs) | Expr::List(ref exprs) => {
                for expr in exprs {
                    Def::collect_locals_from_assign_expr(expr, local_names);
                }
            }
            Expr::Identifier(ref ident) => {
                local_names.insert(ident.node.clone());
            }
            _ => {}
        }
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

    fn to_str(&self) -> String {
        function::to_str(&self.function_type, &self.signature)
    }

    fn to_repr(&self) -> String {
        function::repr(&self.function_type, &self.signature)
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
                self.local_names.clone(),
                Default::default(),
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

        for s in &self.signature {
            let (name, v) = match s {
                FunctionParameter::Normal(ref name) => (name, parser.next_normal(name)?),
                FunctionParameter::WithDefaultValue(ref name, ref default_value) => {
                    (name, parser.next_with_default_value(name, default_value))
                }
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

        match eval_stmt(&self.stmts, &mut ctx) {
            Err(EvalException::Return(_s, ret)) => Ok(ret),
            Err(x) => Err(ValueError::DiagnosedError(x.into())),
            Ok(..) => Ok(Value::new(NoneType::None)),
        }
    }
}
