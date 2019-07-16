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
use crate::eval::{
    eval_stmt, DefLocals, EvalException, EvaluationContext, EvaluationContextEnvironment,
};
use crate::syntax::ast::{AstExpr, AstParameter, AstStatement, AstString, Expr, Statement};
use crate::values::error::ValueError;
use crate::values::function::{FunctionParameter, FunctionType};
use crate::values::none::NoneType;
use crate::values::{function, Immutable, TypedValue, Value, ValueResult};
use codemap::{CodeMap, Spanned};
use linked_hash_map::LinkedHashMap;
use std::collections::HashMap;
use std::convert::TryInto;
use std::iter;
use std::sync::{Arc, Mutex};

/// `def` AST with post-processing suitable for faster excecution
#[doc(hidden)]
#[derive(Debug, Clone)]
pub struct DefCompiled {
    pub(crate) name: AstString,
    pub(crate) params: Vec<AstParameter>,
    pub(crate) suite: AstStatement,
    local_names_to_indices: HashMap<String, usize>,
}

impl DefCompiled {
    pub fn new(name: AstString, params: Vec<AstParameter>, suite: AstStatement) -> DefCompiled {
        let mut local_names_to_indices = HashMap::new();

        for p in &params {
            let len = local_names_to_indices.len();
            local_names_to_indices
                .entry(p.name().to_owned())
                .or_insert(len);
        }

        DefCompiled::collect_locals(&suite, &mut local_names_to_indices);

        let suite = DefCompiled::transform_locals(suite, &local_names_to_indices);

        DefCompiled {
            name,
            params,
            suite,
            local_names_to_indices,
        }
    }

    fn collect_locals(stmt: &AstStatement, local_names_to_indices: &mut HashMap<String, usize>) {
        match stmt.node {
            Statement::Assign(ref dest, ..) => {
                DefCompiled::collect_locals_from_assign_expr(dest, local_names_to_indices);
            }
            Statement::For(ref dest, _, ref body) => {
                DefCompiled::collect_locals_from_assign_expr(dest, local_names_to_indices);
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
            Statement::Load(..) | Statement::Def(..) | Statement::DefCompiled(..) => unreachable!(),
        }
    }

    /// Transform statement replacing local variables access by name with access by index
    fn transform_locals(stmts: AstStatement, locals: &HashMap<String, usize>) -> AstStatement {
        Box::new(Spanned {
            span: stmts.span,
            node: match stmts.node {
                Statement::Assign(left, op, right) => Statement::Assign(
                    DefCompiled::transform_locals_in_expr(left, locals),
                    op,
                    DefCompiled::transform_locals_in_expr(right, locals),
                ),
                Statement::For(var, collection, body) => Statement::For(
                    DefCompiled::transform_locals_in_expr(var, locals),
                    DefCompiled::transform_locals_in_expr(collection, locals),
                    DefCompiled::transform_locals(body, locals),
                ),
                Statement::Statements(stmts) => Statement::Statements(
                    stmts
                        .into_iter()
                        .map(|stmt| DefCompiled::transform_locals(stmt, locals))
                        .collect(),
                ),
                Statement::If(cond, then_block) => Statement::If(
                    DefCompiled::transform_locals_in_expr(cond, locals),
                    DefCompiled::transform_locals(then_block, locals),
                ),
                Statement::IfElse(cond, then_block, else_block) => Statement::IfElse(
                    DefCompiled::transform_locals_in_expr(cond, locals),
                    DefCompiled::transform_locals(then_block, locals),
                    DefCompiled::transform_locals(else_block, locals),
                ),
                s @ Statement::Break | s @ Statement::Continue | s @ Statement::Pass => s,
                Statement::Def(..) | Statement::Load(..) | Statement::DefCompiled(..) => {
                    unreachable!()
                }
                Statement::Expression(expr) => {
                    Statement::Expression(DefCompiled::transform_locals_in_expr(expr, locals))
                }
                Statement::Return(expr) => Statement::Return(
                    expr.map(|expr| DefCompiled::transform_locals_in_expr(expr, locals)),
                ),
            },
        })
    }

    fn collect_locals_from_assign_expr(
        expr: &AstExpr,
        local_names_to_indices: &mut HashMap<String, usize>,
    ) {
        match expr.node {
            Expr::Tuple(ref exprs) | Expr::List(ref exprs) => {
                for expr in exprs {
                    DefCompiled::collect_locals_from_assign_expr(expr, local_names_to_indices);
                }
            }
            Expr::Identifier(ref ident) => {
                let len = local_names_to_indices.len();
                local_names_to_indices
                    .entry(ident.node.clone())
                    .or_insert(len);
            }
            _ => {}
        }
    }

    fn transform_locals_in_expr(expr: AstExpr, locals: &HashMap<String, usize>) -> AstExpr {
        Box::new(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Tuple(exprs) => Expr::Tuple(
                    exprs
                        .into_iter()
                        .map(|expr| DefCompiled::transform_locals_in_expr(expr, locals))
                        .collect(),
                ),
                Expr::List(exprs) => Expr::List(
                    exprs
                        .into_iter()
                        .map(|expr| DefCompiled::transform_locals_in_expr(expr, locals))
                        .collect(),
                ),
                Expr::Set(exprs) => Expr::Set(
                    exprs
                        .into_iter()
                        .map(|expr| DefCompiled::transform_locals_in_expr(expr, locals))
                        .collect(),
                ),
                Expr::Dict(pairs) => Expr::Dict(
                    pairs
                        .into_iter()
                        .map(|(key, value)| {
                            (
                                DefCompiled::transform_locals_in_expr(key, locals),
                                DefCompiled::transform_locals_in_expr(value, locals),
                            )
                        })
                        .collect(),
                ),
                Expr::Identifier(ident) => match locals.get(&ident.node) {
                    Some(&slot) => Expr::Slot(slot, ident),
                    None => Expr::Identifier(ident),
                },
                Expr::Slot(..) => unreachable!(),
                Expr::Dot(left, right) => {
                    Expr::Dot(DefCompiled::transform_locals_in_expr(left, locals), right)
                }
                Expr::Call(function, args, kwargs, star_args, star_star_kwargs) => Expr::Call(
                    DefCompiled::transform_locals_in_expr(function, locals),
                    args.into_iter()
                        .map(|expr| DefCompiled::transform_locals_in_expr(expr, locals))
                        .collect(),
                    kwargs
                        .into_iter()
                        .map(|(name, value)| {
                            (name, DefCompiled::transform_locals_in_expr(value, locals))
                        })
                        .collect(),
                    star_args.map(|expr| DefCompiled::transform_locals_in_expr(expr, locals)),
                    star_star_kwargs
                        .map(|expr| DefCompiled::transform_locals_in_expr(expr, locals)),
                ),
                Expr::ArrayIndirection(array, index) => Expr::ArrayIndirection(
                    DefCompiled::transform_locals_in_expr(array, locals),
                    DefCompiled::transform_locals_in_expr(index, locals),
                ),
                Expr::Slice(array, p1, p2, p3) => Expr::Slice(
                    array,
                    p1.map(|expr| DefCompiled::transform_locals_in_expr(expr, locals)),
                    p2.map(|expr| DefCompiled::transform_locals_in_expr(expr, locals)),
                    p3.map(|expr| DefCompiled::transform_locals_in_expr(expr, locals)),
                ),
                Expr::Not(expr) => Expr::Not(DefCompiled::transform_locals_in_expr(expr, locals)),
                Expr::Minus(expr) => {
                    Expr::Minus(DefCompiled::transform_locals_in_expr(expr, locals))
                }
                Expr::Plus(expr) => Expr::Plus(DefCompiled::transform_locals_in_expr(expr, locals)),
                Expr::Op(op, left, right) => Expr::Op(
                    op,
                    DefCompiled::transform_locals_in_expr(left, locals),
                    DefCompiled::transform_locals_in_expr(right, locals),
                ),
                Expr::If(cond, then_expr, else_expr) => Expr::If(
                    DefCompiled::transform_locals_in_expr(cond, locals),
                    DefCompiled::transform_locals_in_expr(then_expr, locals),
                    DefCompiled::transform_locals_in_expr(else_expr, locals),
                ),
                n @ Expr::IntLiteral(..) | n @ Expr::StringLiteral(..) => n,
                n @ Expr::DictComprehension(..)
                | n @ Expr::ListComprehension(..)
                | n @ Expr::SetComprehension(..) => {
                    // TODO: do the same access-by-index optimization for compr locals.
                    // TODO: access parent scope (function) variables by index, not by name.
                    n
                }
            },
        })
    }
}

/// Starlark function internal representation and implementation of [`TypedValue`].
pub(crate) struct Def {
    signature: Vec<FunctionParameter>,
    function_type: FunctionType,
    captured_env: Environment,
    map: Arc<Mutex<CodeMap>>,
    stmt: DefCompiled,
}

impl Def {
    pub fn new(
        module: String,
        signature: Vec<FunctionParameter>,
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
                DefLocals::new(&self.stmt.local_names_to_indices),
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

        match eval_stmt(&self.stmt.suite, &mut ctx) {
            Err(EvalException::Return(_s, ret)) => Ok(ret),
            Err(x) => Err(ValueError::DiagnosedError(x.into())),
            Ok(..) => Ok(Value::new(NoneType::None)),
        }
    }
}
