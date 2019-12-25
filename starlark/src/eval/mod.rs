// Copyright 2018 The Starlark in Rust Authors
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

//! Evaluation environment, provide converters from Ast* element to value.
//!
//! # <a name="build_file"></a>Starlark and BUILD dialect
//!
//! All evaluation function can evaluate the full Starlark language (i.e. Bazel's
//! .bzl files) or the BUILD file dialect (i.e. used to interpret Bazel's BUILD file).
//! The BUILD dialect does not allow `def` statements.
use crate::environment::Environment;
use crate::environment::TypeValues;
use crate::eval::call_stack::CallStack;
use crate::eval::compr::eval_one_dimensional_comprehension;
use crate::eval::def::Def;
use crate::eval::def::ParameterCompiled;
use crate::eval::expr::AssignTargetExprCompiled;
use crate::eval::expr::AstAssignTargetExprCompiled;
use crate::eval::expr::AstAugmentedAssignTargetExprCompiled;
use crate::eval::expr::AstExprCompiled;
use crate::eval::expr::AugmentedAssignTargetExprCompiled;
use crate::eval::expr::ExprCompiled;
use crate::eval::expr::GlobalOrSlot;
use crate::eval::locals::Locals;
use crate::eval::module::Module;
use crate::eval::stmt::AstStatementCompiled;
use crate::eval::stmt::BlockCompiled;
use crate::eval::stmt::StatementCompiled;
use crate::syntax::ast::BinOp;
use crate::syntax::ast::*;
use crate::syntax::dialect::Dialect;
use crate::syntax::errors::SyntaxError;
use crate::syntax::lexer::{LexerIntoIter, LexerItem};
use crate::syntax::parser::{parse, parse_file, parse_lexer};
use crate::values::context::EvaluationContext;
use crate::values::context::EvaluationContextEnvironment;
use crate::values::context::EvaluationContextEnvironmentLocal;
use crate::values::context::EvaluationContextEnvironmentModule;
use crate::values::context::IndexedLocals;
use crate::values::dict::Dictionary;
use crate::values::error::ValueError;
use crate::values::function::FunctionParameter;
use crate::values::function::FunctionSignature;
use crate::values::function::WrappedMethod;
use crate::values::none::NoneType;
use crate::values::*;
use codemap::{CodeMap, Span, Spanned};
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use linked_hash_map::LinkedHashMap;
use std::cmp::Ordering;
use std::sync::{Arc, Mutex};

fn eval_vector<E: EvaluationContextEnvironment>(
    v: &[AstExprCompiled],
    ctx: &mut EvaluationContext<E>,
) -> Result<Vec<Value>, EvalException> {
    v.into_iter().map(|s| eval_expr(s, ctx)).collect()
}

// TODO: move that code in some common error code list?
// CE prefix = Critical Evaluation
#[doc(hidden)]
pub const BREAK_ERROR_CODE: &str = "CE00";
#[doc(hidden)]
pub const CONTINUE_ERROR_CODE: &str = "CE01";
#[doc(hidden)]
pub const RETURN_ERROR_CODE: &str = "CE02";
#[doc(hidden)]
pub const INCORRECT_LEFT_VALUE_ERROR_CODE: &str = "CE03";
#[doc(hidden)]
pub const INCORRECT_UNPACK_ERROR_CODE: &str = "CE04";
#[doc(hidden)]
pub const RECURSION_ERROR_CODE: &str = "CE05";

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum EvalException {
    // Flow control statement reached
    Break(Span),
    Continue(Span),
    Return(Span, Value),
    // Error bubbling up as diagnostics
    DiagnosedError(Diagnostic),
    // Expression used as left value cannot be assigned
    IncorrectLeftValue(Span),
    // Incorrect number of value to unpack (expected, got)
    IncorrectNumberOfValueToUnpack(Span, i64, i64),
    // Recursion
    Recursion(Span, String, CallStack),
}

impl From<Diagnostic> for EvalException {
    fn from(diagnostic: Diagnostic) -> Self {
        EvalException::DiagnosedError(diagnostic)
    }
}

type EvalResult = Result<Value, EvalException>;

/// An object with [`Span`]
trait AsSpan {
    fn as_span(&self) -> Span;
}

impl AsSpan for Span {
    fn as_span(&self) -> Span {
        *self
    }
}

impl<T> AsSpan for Spanned<T> {
    fn as_span(&self) -> Span {
        self.span
    }
}

impl<T> AsSpan for Box<Spanned<T>> {
    fn as_span(&self) -> Span {
        self.span
    }
}

/// Convert syntax error to spanned evaluation exception
fn t<T, E: SyntaxError, S: AsSpan>(r: Result<T, E>, spanned: &S) -> Result<T, EvalException> {
    match r {
        Ok(v) => Ok(v),
        Err(e) => Err(EvalException::DiagnosedError(
            e.to_diagnostic(spanned.as_span()),
        )),
    }
}

impl Into<Diagnostic> for EvalException {
    fn into(self) -> Diagnostic {
        match self {
            EvalException::DiagnosedError(e) => e,
            EvalException::Break(s) => Diagnostic {
                level: Level::Error,
                message: "Break statement used outside of a loop".to_owned(),
                code: Some(BREAK_ERROR_CODE.to_owned()),
                spans: vec![SpanLabel {
                    span: s,
                    style: SpanStyle::Primary,
                    label: None,
                }],
            },
            EvalException::Continue(s) => Diagnostic {
                level: Level::Error,
                message: "Continue statement used outside of a loop".to_owned(),
                code: Some(CONTINUE_ERROR_CODE.to_owned()),
                spans: vec![SpanLabel {
                    span: s,
                    style: SpanStyle::Primary,
                    label: None,
                }],
            },
            EvalException::Return(s, ..) => Diagnostic {
                level: Level::Error,
                message: "Return statement used outside of a function call".to_owned(),
                code: Some(RETURN_ERROR_CODE.to_owned()),
                spans: vec![SpanLabel {
                    span: s,
                    style: SpanStyle::Primary,
                    label: None,
                }],
            },
            EvalException::IncorrectLeftValue(s) => Diagnostic {
                level: Level::Error,
                message: "Incorrect expression as left value".to_owned(),
                code: Some(INCORRECT_LEFT_VALUE_ERROR_CODE.to_owned()),
                spans: vec![SpanLabel {
                    span: s,
                    style: SpanStyle::Primary,
                    label: None,
                }],
            },
            EvalException::IncorrectNumberOfValueToUnpack(s, expected, got) => Diagnostic {
                level: Level::Error,
                message: format!("Unpacked {} values but expected {}", got, expected),
                code: Some(INCORRECT_UNPACK_ERROR_CODE.to_owned()),
                spans: vec![SpanLabel {
                    span: s,
                    style: SpanStyle::Primary,
                    label: None,
                }],
            },
            EvalException::Recursion(s, f, stack) => Diagnostic {
                level: Level::Error,
                message: format!(
                    "Function {} recursed, call stack:{}",
                    f,
                    stack.print_with_newline_before()
                ),
                code: Some(RECURSION_ERROR_CODE.to_owned()),
                spans: vec![SpanLabel {
                    span: s,
                    style: SpanStyle::Primary,
                    label: Some("Recursive call".to_owned()),
                }],
            },
        }
    }
}

/// A trait for loading file using the load statement path.
pub trait FileLoader {
    /// Open the file given by the load statement `path`.
    fn load(&self, path: &str, type_values: &TypeValues) -> Result<Environment, EvalException>;
}

fn eval_bin_op<E: EvaluationContextEnvironment>(
    expr: &AstExprCompiled,
    op: BinOp,
    l: &AstExprCompiled,
    r: &AstExprCompiled,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    let l = eval_expr(l, context)?;
    let r = eval_expr(r, context)?;

    t(
        match op {
            BinOp::EqualsTo => l.equals(&r).map(Value::new),
            BinOp::Different => l.equals(&r).map(|b| Value::new(!b)),
            BinOp::LowerThan => l.compare(&r).map(|c| Value::new(c == Ordering::Less)),
            BinOp::GreaterThan => l.compare(&r).map(|c| Value::new(c == Ordering::Greater)),
            BinOp::LowerOrEqual => l.compare(&r).map(|c| Value::new(c != Ordering::Greater)),
            BinOp::GreaterOrEqual => l.compare(&r).map(|c| Value::new(c != Ordering::Less)),
            BinOp::In => r.is_in(&l).map(Value::new),
            BinOp::NotIn => r.is_in(&l).map(|r| Value::new(!r)),
            BinOp::Substraction => l.sub(r),
            BinOp::Addition => l.add(r),
            BinOp::Multiplication => l.mul(r),
            BinOp::Percent => l.percent(r),
            BinOp::Division => {
                // No types currently support / so always error.
                let err = ValueError::OperationNotSupported {
                    op: "/".to_string(),
                    left: l.get_type().to_string(),
                    right: Some(r.get_type().to_string()),
                };
                return Err(EvalException::DiagnosedError(err.to_diagnostic(expr.span)));
            }
            BinOp::FloorDivision => l.floor_div(r),
            BinOp::Pipe => l.pipe(r),
        },
        expr,
    )
}

fn eval_slice<E: EvaluationContextEnvironment>(
    this: &AstExprCompiled,
    a: &AstExprCompiled,
    start: &Option<AstExprCompiled>,
    stop: &Option<AstExprCompiled>,
    stride: &Option<AstExprCompiled>,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    let a = eval_expr(a, context)?;
    let start = match start {
        Some(ref e) => Some(eval_expr(e, context)?),
        None => None,
    };
    let stop = match stop {
        Some(ref e) => Some(eval_expr(e, context)?),
        None => None,
    };
    let stride = match stride {
        Some(ref e) => Some(eval_expr(e, context)?),
        None => None,
    };
    t(a.slice(start, stop, stride), this)
}

fn eval_call<E: EvaluationContextEnvironment>(
    this: &AstExprCompiled,
    e: &AstExprCompiled,
    pos: &[AstExprCompiled],
    named: &[(AstString, AstExprCompiled)],
    args: &Option<AstExprCompiled>,
    kwargs: &Option<AstExprCompiled>,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    let npos = eval_vector(pos, context)?;
    let mut nnamed = LinkedHashMap::new();
    for &(ref k, ref v) in named.iter() {
        nnamed.insert(k.node.clone(), eval_expr(v, context)?);
    }
    let nargs = if let Some(ref x) = args {
        Some(eval_expr(x, context)?)
    } else {
        None
    };
    let nkwargs = if let Some(ref x) = kwargs {
        Some(eval_expr(x, context)?)
    } else {
        None
    };
    let f = eval_expr(e, context)?;
    if context.call_stack.contains(f.function_id()) {
        let mut new_stack = context.call_stack.clone();
        new_stack.push(f.clone(), context.map.clone(), this.span.low());
        Err(EvalException::Recursion(this.span, f.to_repr(), new_stack))
    } else {
        context
            .call_stack
            .push(f.clone(), context.map.clone(), this.span.low());
        let r = t(
            eval_expr(e, context)?.call(
                context.call_stack,
                context.type_values,
                npos,
                nnamed,
                nargs,
                nkwargs,
            ),
            this,
        );
        context.call_stack.pop();
        r
    }
}

fn eval_dot<E: EvaluationContextEnvironment>(
    this: &AstExprCompiled,
    e: &AstExprCompiled,
    s: &AstString,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    let left = eval_expr(e, context)?;
    if let Some(v) = context.type_values.get_type_value(&left, &s.node) {
        if v.get_type() == "function" {
            // Insert self so the method see the object it is acting on
            Ok(WrappedMethod::new(left, v))
        } else {
            Ok(v)
        }
    } else {
        t(left.get_attr(&s.node), this)
    }
}

enum TransformedExpr {
    Dot(Value, String, Span),
    ArrayIndirection(Value, Value, Span),
    Slot(usize, AstString),
}

fn set_transformed<E: EvaluationContextEnvironment>(
    transformed: &TransformedExpr,
    context: &mut EvaluationContext<E>,
    new_value: Value,
) -> EvalResult {
    let ok = Ok(Value::new(NoneType::None));
    match transformed {
        TransformedExpr::Dot(ref e, ref s, ref span) => {
            t(e.clone().set_attr(&s, new_value), span)?;
            ok
        }
        TransformedExpr::ArrayIndirection(ref e, ref idx, ref span) => {
            t(e.clone().set_at(idx.clone(), new_value), span)?;
            ok
        }
        TransformedExpr::Slot(slot, ident) => {
            context.env.set_local(*slot, &ident.node, new_value);
            ok
        }
    }
}

fn eval_transformed<E: EvaluationContextEnvironment>(
    transformed: &TransformedExpr,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    match transformed {
        TransformedExpr::Dot(ref left, ref s, ref span) => {
            if let Some(v) = context.type_values.get_type_value(left, &s) {
                if v.get_type() == "function" {
                    // Insert self so the method see the object it is acting on
                    Ok(WrappedMethod::new(left.clone(), v))
                } else {
                    Ok(v)
                }
            } else {
                t(left.get_attr(&s), span)
            }
        }
        TransformedExpr::ArrayIndirection(ref e, ref idx, ref span) => t(e.at(idx.clone()), span),
        TransformedExpr::Slot(slot, ident) => t(context.env.get_local(*slot, &ident.node), ident),
    }
}

fn make_set<E: EvaluationContextEnvironment>(
    values: Vec<Value>,
    context: &EvaluationContext<E>,
    span: Span,
) -> EvalResult {
    context
        .env
        .env()
        .make_set(values)
        .map_err(|err| EvalException::DiagnosedError(err.to_diagnostic(span)))
}

// An intermediate transformation that tries to evaluate parameters of function / indices.
// It is used to cache result of LHS in augmented assignment.
// This transformation by default should be a deep copy (clone).
fn transform<E: EvaluationContextEnvironment>(
    expr: &AstAugmentedAssignTargetExprCompiled,
    context: &mut EvaluationContext<E>,
) -> Result<TransformedExpr, EvalException> {
    match &expr.node {
        AugmentedAssignTargetExprCompiled::Dot(ref e, ref s) => Ok(TransformedExpr::Dot(
            eval_expr(e, context)?,
            s.node.clone(),
            expr.span,
        )),
        AugmentedAssignTargetExprCompiled::ArrayIndirection(ref e, ref idx) => {
            Ok(TransformedExpr::ArrayIndirection(
                eval_expr(e, context)?,
                eval_expr(idx, context)?,
                expr.span,
            ))
        }
        AugmentedAssignTargetExprCompiled::Slot(index, ref ident) => {
            Ok(TransformedExpr::Slot(*index, ident.clone()))
        }
    }
}

// Evaluate the AST in global context, create local context, and continue evaluating in local
fn eval_expr_local<E: EvaluationContextEnvironment>(
    expr: &AstExprCompiled,
    locals: &Locals,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    let mut ctx = EvaluationContext {
        call_stack: context.call_stack,
        env: EvaluationContextEnvironmentLocal {
            // Note assertion that we where in module context
            globals: context.env.assert_module_env().env.clone(),
            locals: IndexedLocals::new(locals),
        },
        type_values: context.type_values,
        map: context.map.clone(),
    };
    eval_expr(expr, &mut ctx)
}

// Evaluate the AST element, i.e. mutate the environment and return an evaluation result
fn eval_expr<E: EvaluationContextEnvironment>(
    expr: &AstExprCompiled,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    match expr.node {
        ExprCompiled::Tuple(ref v) => {
            let r = eval_vector(v, context)?;
            Ok(Value::new(tuple::Tuple::new(r)))
        }
        ExprCompiled::Dot(ref e, ref s) => eval_dot(expr, e, s, context),
        ExprCompiled::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
            eval_call(expr, e, pos, named, args, kwargs, context)
        }
        ExprCompiled::ArrayIndirection(ref e, ref idx) => {
            let idx = eval_expr(idx, context)?;
            t(eval_expr(e, context)?.at(idx), expr)
        }
        ExprCompiled::Slice(ref a, ref start, ref stop, ref stride) => {
            eval_slice(expr, a, start, stop, stride, context)
        }
        ExprCompiled::Name(ref name) => match &name.node {
            GlobalOrSlot::Global(ref i) => t(context.env.get_global(i), name),
            GlobalOrSlot::Slot(slot, ref i) => t(context.env.get_local(*slot, i), name),
        },
        ExprCompiled::Value(ref v) => Ok(v.clone()),
        ExprCompiled::Not(ref s) => Ok(Value::new(!eval_expr(s, context)?.to_bool())),
        ExprCompiled::Minus(ref s) => t(eval_expr(s, context)?.minus(), expr),
        ExprCompiled::Plus(ref s) => t(eval_expr(s, context)?.plus(), expr),
        ExprCompiled::Or(ref l, ref r) => {
            let l = eval_expr(l, context)?;
            Ok(if l.to_bool() {
                l
            } else {
                eval_expr(r, context)?
            })
        }
        ExprCompiled::And(ref l, ref r) => {
            let l = eval_expr(l, context)?;
            Ok(if !l.to_bool() {
                l
            } else {
                eval_expr(r, context)?
            })
        }
        ExprCompiled::Op(op, ref l, ref r) => eval_bin_op(expr, op, l, r, context),
        ExprCompiled::If(ref cond, ref v1, ref v2) => {
            if eval_expr(cond, context)?.to_bool() {
                eval_expr(v1, context)
            } else {
                eval_expr(v2, context)
            }
        }
        ExprCompiled::List(ref v) => {
            let r = eval_vector(v, context)?;
            Ok(Value::from(r))
        }
        ExprCompiled::Dict(ref v) => {
            let mut r = dict::Dictionary::new();
            for s in v.iter() {
                t(
                    r.set_at(eval_expr(&s.0, context)?, eval_expr(&s.1, context)?),
                    expr,
                )?
            }
            Ok(r)
        }
        ExprCompiled::Set(ref v) => {
            let mut values = Vec::with_capacity(v.len());
            for s in v {
                values.push(eval_expr(s, context)?);
            }
            make_set(values, context, expr.span)
        }
        ExprCompiled::ListComprehension(ref expr, ref clauses) => {
            let mut list = Vec::new();
            eval_one_dimensional_comprehension(
                &mut |context| {
                    list.push(eval_expr(expr, context)?);
                    Ok(())
                },
                clauses,
                context,
            )?;
            Ok(Value::from(list))
        }
        ExprCompiled::SetComprehension(ref expr, ref clauses) => {
            let mut values = Vec::new();
            eval_one_dimensional_comprehension(
                &mut |context| {
                    values.push(eval_expr(expr, context)?);
                    Ok(())
                },
                clauses,
                context,
            )?;
            make_set(values, context, expr.span)
        }
        ExprCompiled::DictComprehension((ref k, ref v), ref clauses) => {
            let mut dict = Dictionary::new_typed();
            eval_one_dimensional_comprehension(
                &mut |context| {
                    t(
                        dict.insert(eval_expr(k, context)?, eval_expr(v, context)?),
                        &expr.span,
                    )
                },
                clauses,
                context,
            )?;
            Ok(Value::new(dict))
        }
        ExprCompiled::Local(ref expr, ref locals) => eval_expr_local(expr, locals, context),
    }
}

// Perform an assignment on the LHS represented by this AST element
fn set_expr<E: EvaluationContextEnvironment>(
    expr: &AstAssignTargetExprCompiled,
    context: &mut EvaluationContext<E>,
    new_value: Value,
) -> EvalResult {
    let ok = Ok(Value::new(NoneType::None));
    match expr.node {
        AssignTargetExprCompiled::Subtargets(ref v) => {
            // TODO: the span here should probably include the rvalue
            let new_values: Vec<Value> = t(new_value.iter(), expr)?.iter().collect();
            let l = v.len();
            if new_values.len() != l {
                Err(EvalException::IncorrectNumberOfValueToUnpack(
                    expr.span,
                    l as i64,
                    new_values.len() as i64,
                ))
            } else {
                let mut it1 = v.iter();
                let mut it2 = new_values.into_iter();
                for _ in 0..l {
                    set_expr(it1.next().unwrap(), context, it2.next().unwrap())?;
                }
                ok
            }
        }
        AssignTargetExprCompiled::Dot(ref e, ref s) => {
            t(eval_expr(e, context)?.set_attr(&(s.node), new_value), expr)?;
            ok
        }
        AssignTargetExprCompiled::Name(ref name) => match &name.node {
            GlobalOrSlot::Global(ref i) => {
                t(context.env.assert_module_env().env.set(&i, new_value), expr)?;
                ok
            }
            GlobalOrSlot::Slot(slot, ref i) => {
                context.env.set_local(*slot, &i, new_value);
                ok
            }
        },
        AssignTargetExprCompiled::ArrayIndirection(ref e, ref idx) => {
            t(
                eval_expr(e, context)?.set_at(eval_expr(idx, context)?, new_value),
                expr,
            )?;
            ok
        }
    }
}

fn eval_assign_modify<E: EvaluationContextEnvironment>(
    stmt: &AstStatementCompiled,
    lhs: &AstAugmentedAssignTargetExprCompiled,
    rhs: &AstExprCompiled,
    context: &mut EvaluationContext<E>,
    op: AugmentedAssignOp,
) -> EvalResult
where
{
    let op = match op {
        AugmentedAssignOp::Increment => Value::add,
        AugmentedAssignOp::Decrement => Value::sub,
        AugmentedAssignOp::Multiplier => Value::mul,
        AugmentedAssignOp::Divider => Value::div,
        AugmentedAssignOp::FloorDivider => Value::floor_div,
        AugmentedAssignOp::Percent => Value::percent,
    };

    let lhs = transform(lhs, context)?;
    let l = eval_transformed(&lhs, context)?;
    let r = eval_expr(rhs, context)?;
    set_transformed(&lhs, context, t(op(&l, r), stmt)?)
}

fn eval_stmt<E: EvaluationContextEnvironment>(
    stmt: &AstStatementCompiled,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    match stmt.node {
        StatementCompiled::Break => Err(EvalException::Break(stmt.span)),
        StatementCompiled::Continue => Err(EvalException::Continue(stmt.span)),
        StatementCompiled::Return(Some(ref e)) => {
            Err(EvalException::Return(stmt.span, eval_expr(e, context)?))
        }
        StatementCompiled::Return(None) => {
            Err(EvalException::Return(stmt.span, Value::new(NoneType::None)))
        }
        StatementCompiled::Expression(ref e) => eval_expr(e, context),
        StatementCompiled::Assign(ref lhs, ref rhs) => {
            let rhs = eval_expr(rhs, context)?;
            set_expr(lhs, context, rhs)
        }
        StatementCompiled::AugmentedAssign(ref lhs, op, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, op)
        }
        StatementCompiled::IfElse(ref cond, ref st1, ref st2) => {
            if eval_expr(cond, context)?.to_bool() {
                eval_block(st1, context)
            } else {
                eval_block(st2, context)
            }
        }
        StatementCompiled::For(ref e1, ref e2, ref st) => {
            let iterable = eval_expr(e2, context)?;
            let mut result = Ok(Value::new(NoneType::None));
            for v in &t(iterable.iter(), &e2.span)? {
                set_expr(e1, context, v)?;
                match eval_block(st, context) {
                    Err(EvalException::Break(..)) => break,
                    Err(EvalException::Continue(..)) => (),
                    Err(x) => {
                        result = Err(x);
                        break;
                    }
                    _ => (),
                }
            }
            result
        }
        StatementCompiled::Def(ref stmt) => {
            let mut p = Vec::new();
            for x in &stmt.params {
                p.push(match x.node {
                    ParameterCompiled::Normal(ref n) => FunctionParameter::Normal(n.node.clone()),
                    ParameterCompiled::WithDefaultValue(ref n, ref v) => {
                        FunctionParameter::WithDefaultValue(n.node.clone(), eval_expr(v, context)?)
                    }
                    ParameterCompiled::Args(ref n) => FunctionParameter::ArgsArray(n.node.clone()),
                    ParameterCompiled::KWArgs(ref n) => {
                        FunctionParameter::KWArgsDict(n.node.clone())
                    }
                })
            }
            let f = Def::new(
                context.env.assert_module_env().env.name(),
                FunctionSignature::new(p, 0),
                stmt.clone(),
                context.map.clone(),
                context.env.assert_module_env().env.clone(),
            );
            t(
                context
                    .env
                    .assert_module_env()
                    .env
                    .set(&stmt.name.node, f.clone()),
                &stmt.name,
            )?;
            Ok(f)
        }
        StatementCompiled::Load(ref name, ref v) => {
            let loadenv = context
                .env
                .assert_module_env()
                .loader
                .load(name, context.type_values)?;
            loadenv.freeze();
            for &(ref new_name, ref orig_name) in v.iter() {
                t(
                    context.env.assert_module_env().env.import_symbol(
                        &loadenv,
                        &orig_name.node,
                        &new_name.node,
                    ),
                    &new_name.span.merge(orig_name.span),
                )?
            }
            Ok(Value::new(NoneType::None))
        }
    }
}

fn eval_block<E: EvaluationContextEnvironment>(
    block: &BlockCompiled,
    context: &mut EvaluationContext<E>,
) -> EvalResult {
    let mut r = Value::new(NoneType::None);
    for stmt in &block.0 {
        r = eval_stmt(stmt, context)?;
    }
    Ok(r)
}

fn eval_module(
    module: &Module,
    env: &mut Environment,
    type_values: &TypeValues,
    map: Arc<Mutex<CodeMap>>,
    loader: &dyn FileLoader,
) -> EvalResult {
    let mut call_stack = CallStack::default();
    let mut context = EvaluationContext {
        env: EvaluationContextEnvironmentModule {
            env: env.clone(),
            loader,
        },
        type_values,
        call_stack: &mut call_stack,
        map,
    };
    eval_block(&module.0, &mut context)
}

/// Evaluate a content provided by a custom Lexer, mutate the environment accordingly and return
/// the evaluated value.
///
/// # Arguments
///
/// * map: the codemap object used for diagnostics
/// * filename: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate, for diagnostics
/// * dialect: starlark syntax dialect
/// * lexer: the custom lexer to use
/// * env: the environment to mutate during the evaluation
/// * file_loader: the [`FileLoader`] to react to `load()` statements.
pub fn eval_lexer<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>>(
    map: &Arc<Mutex<CodeMap>>,
    filename: &str,
    content: &str,
    dialect: Dialect,
    lexer: T2,
    env: &mut Environment,
    type_values: &TypeValues,
    file_loader: &dyn FileLoader,
) -> Result<Value, Diagnostic> {
    match eval_module(
        &parse_lexer(map, filename, content, dialect, lexer)?,
        env,
        type_values,
        map.clone(),
        file_loader,
    ) {
        Ok(v) => Ok(v),
        Err(p) => Err(p.into()),
    }
}

/// Evaluate a string content, mutate the environment accordingly and return the evaluated value.
///
/// # Arguments
///
/// * map: the codemap object used for diagnostics
/// * path: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate
/// * build: set to true if you want to evaluate a BUILD file or false to evaluate a .bzl file.
///   More information about the difference can be found in [this module's
///   documentation](index.html#build_file).
/// * env: the environment to mutate during the evaluation
/// * file_loader: the [`FileLoader`] to react to `load()` statements.
pub fn eval(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    content: &str,
    build: Dialect,
    env: &mut Environment,
    type_values: &TypeValues,
    file_loader: &dyn FileLoader,
) -> Result<Value, Diagnostic> {
    match eval_module(
        &parse(map, path, content, build)?,
        env,
        type_values,
        map.clone(),
        file_loader,
    ) {
        Ok(v) => Ok(v),
        Err(p) => Err(p.into()),
    }
}

/// Evaluate a file, mutate the environment accordingly and return the evaluated value.
///
/// # Arguments
///
/// * map: the codemap object used for diagnostics
/// * path: the file to parse and evaluate
/// * build: set to true if you want to evaluate a BUILD file or false to evaluate a .bzl file.
///   More information about the difference can be found in [this module's
///   documentation](index.html#build_file).
/// * env: the environment to mutate during the evaluation
/// * file_loader: the [`FileLoader`] to react to `load()` statements.
pub fn eval_file(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    build: Dialect,
    env: &mut Environment,
    type_values: &TypeValues,
    file_loader: &dyn FileLoader,
) -> Result<Value, Diagnostic> {
    match eval_module(
        &parse_file(map, path, build)?,
        env,
        type_values,
        map.clone(),
        file_loader,
    ) {
        Ok(v) => Ok(v),
        Err(p) => Err(p.into()),
    }
}

pub mod interactive;
pub mod noload;
pub mod simple;

pub mod call_stack;

#[cfg(test)]
mod tests;

pub(crate) mod compiler;
pub(crate) mod compr;
pub(crate) mod def;
pub(crate) mod expr;
pub(crate) mod locals;
pub mod module;
pub mod stmt;
