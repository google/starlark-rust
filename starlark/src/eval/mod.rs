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
use crate::environment::{Environment, EnvironmentError, TypeValues};
use crate::eval::call_stack::CallStack;
use crate::syntax::ast::*;
use crate::syntax::ast::{AstExpr, AstStatement};
use crate::syntax::dialect::Dialect;
use crate::syntax::errors::SyntaxError;
use crate::syntax::lexer::{LexerIntoIter, LexerItem};
use crate::syntax::parser::{parse, parse_file, parse_lexer};
use crate::values::dict::Dictionary;
use crate::values::error::ValueError;
use crate::values::function::{FunctionArg, FunctionParameter};
use crate::values::none::NoneType;
use crate::values::*;
use codemap::{CodeMap, Span, Spanned};
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use linked_hash_map::LinkedHashMap;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

macro_rules! eval_vector {
    ($v:expr, $ctx:expr) => {{
        let mut r = Vec::new();
        for s in $v.iter() {
            r.push(eval_expr(s, $ctx)?)
        }
        r
    }};
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
pub trait FileLoader: 'static {
    /// Open the file given by the load statement `path`.
    fn load(&self, path: &str) -> Result<Environment, EvalException>;
}

/// Stacked environment for [`EvaluationContext`].
pub(crate) enum EvaluationContextEnvironment {
    /// Module-level
    Module(Environment),
    /// Function-level
    Function(String, Environment, RefCell<HashMap<String, Value>>),
    /// Scope inside function, e. g. list comprenension
    Nested(
        String,
        Rc<EvaluationContextEnvironment>,
        RefCell<HashMap<String, Value>>,
    ),
}

impl EvaluationContextEnvironment {
    fn env(&self) -> &Environment {
        match self {
            EvaluationContextEnvironment::Module(ref env)
            | EvaluationContextEnvironment::Function(_, ref env, ..) => env,
            EvaluationContextEnvironment::Nested(_, ref parent, _) => parent.env(),
        }
    }

    fn make_set(&self, values: Vec<Value>) -> ValueResult {
        self.env().make_set(values)
    }

    fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        match self {
            EvaluationContextEnvironment::Module(env) => env.get(name),
            EvaluationContextEnvironment::Function(_, env, locals) => {
                match locals.borrow().get(name).cloned() {
                    Some(v) => Ok(v),
                    None => env.get(name),
                }
            }
            EvaluationContextEnvironment::Nested(_, parent, locals) => {
                match locals.borrow().get(name).cloned() {
                    Some(v) => Ok(v),
                    None => parent.get(name),
                }
            }
        }
    }

    fn set(&self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        match self {
            EvaluationContextEnvironment::Module(env) => env.set(name, value),
            EvaluationContextEnvironment::Function(_, _, locals)
            | EvaluationContextEnvironment::Nested(_, _, locals) => {
                // TODO: check that local slot was previously allocated
                locals.borrow_mut().insert(name.to_owned(), value);
                Ok(())
            }
        }
    }

    fn name(&self) -> String {
        match self {
            EvaluationContextEnvironment::Module(env) => env.name(),
            EvaluationContextEnvironment::Function(name, ..)
            | EvaluationContextEnvironment::Nested(name, ..) => name.clone(),
        }
    }

    fn assert_module_env(&self) -> &Environment {
        match self {
            EvaluationContextEnvironment::Module(env) => env,
            EvaluationContextEnvironment::Function(..)
            | EvaluationContextEnvironment::Nested(..) => {
                unreachable!("this function is meant to be called only on module level")
            }
        }
    }
}

/// A structure holding all the data about the evaluation context
/// (scope, load statement resolver, ...)
pub struct EvaluationContext {
    // Locals and captured context.
    env: Rc<EvaluationContextEnvironment>,
    // Globals used to resolve type values, provided by the caller.
    type_values: TypeValues,
    loader: Rc<dyn FileLoader>,
    call_stack: CallStack,
    map: Arc<Mutex<CodeMap>>,
}

impl EvaluationContext {
    fn new<T: FileLoader>(
        env: Environment,
        type_values: TypeValues,
        loader: T,
        map: Arc<Mutex<CodeMap>>,
    ) -> Self {
        EvaluationContext {
            call_stack: CallStack::default(),
            env: Rc::new(EvaluationContextEnvironment::Module(env)),
            type_values,
            loader: Rc::new(loader),
            map,
        }
    }

    fn child(&self, name: &str) -> EvaluationContext {
        EvaluationContext {
            env: Rc::new(EvaluationContextEnvironment::Nested(
                name.to_owned(),
                self.env.clone(),
                Default::default(),
            )),
            type_values: self.type_values.clone(),
            call_stack: self.call_stack.clone(),
            loader: Rc::new(UnreachableFileLoader),
            map: self.map.clone(),
        }
    }
}

/// File loader used in child environments (function eval or list or dict comprehension).
///
/// `load` statement is top level only, so child environments should not use
/// this file loader.
struct UnreachableFileLoader;

impl FileLoader for UnreachableFileLoader {
    fn load(&self, _path: &str) -> Result<Environment, EvalException> {
        // If we reach here, this is a bug.
        unreachable!();
    }
}

fn eval_comprehension_clause(
    context: &mut EvaluationContext,
    e: &AstExpr,
    clauses: &[AstClause],
) -> Result<Vec<Value>, EvalException> {
    let mut result = Vec::new();
    if let Some((c, tl)) = clauses.split_first() {
        match c.node {
            Clause::If(ref cond) => {
                if eval_expr(cond, context)?.to_bool() {
                    if tl.is_empty() {
                        result.push(eval_expr(e, context)?);
                    } else {
                        let mut other = eval_comprehension_clause(context, e, tl)?;
                        result.append(&mut other);
                    }
                };
            }
            Clause::For(ref k, ref v) => {
                let mut iterable = eval_expr(v, context)?;
                iterable.freeze_for_iteration();
                for i in &t(iterable.iter(), c)? {
                    set_expr(k, context, i)?;
                    if tl.is_empty() {
                        result.push(eval_expr(e, context)?);
                    } else {
                        let mut other = eval_comprehension_clause(context, e, tl)?;
                        result.append(&mut other);
                    }
                }
                iterable.unfreeze_for_iteration();
            }
        }
    }
    Ok(result)
}

fn eval_compare<F>(
    this: &AstExpr,
    left: &AstExpr,
    right: &AstExpr,
    cmp: F,
    context: &mut EvaluationContext,
) -> EvalResult
where
    F: Fn(Ordering) -> bool,
{
    let l = eval_expr(left, context)?;
    let r = eval_expr(right, context)?;
    Ok(Value::new(cmp(t(l.compare(&r), this)?)))
}

fn eval_equals<F>(
    this: &AstExpr,
    left: &AstExpr,
    right: &AstExpr,
    cmp: F,
    context: &mut EvaluationContext,
) -> EvalResult
where
    F: Fn(bool) -> bool,
{
    let l = eval_expr(left, context)?;
    let r = eval_expr(right, context)?;
    Ok(Value::new(cmp(t(
        l.equals(&r).map_err(Into::<ValueError>::into),
        this,
    )?)))
}

fn eval_slice(
    this: &AstExpr,
    a: &AstExpr,
    start: &Option<AstExpr>,
    stop: &Option<AstExpr>,
    stride: &Option<AstExpr>,
    context: &mut EvaluationContext,
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

fn eval_call(
    this: &AstExpr,
    e: &AstExpr,
    pos: &[AstExpr],
    named: &[(AstString, AstExpr)],
    args: &Option<AstExpr>,
    kwargs: &Option<AstExpr>,
    context: &mut EvaluationContext,
) -> EvalResult {
    let npos = eval_vector!(pos, context);
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
    let fname = f.to_repr();
    let descr = f.to_str();
    let mut new_stack = context.call_stack.clone();
    if context.call_stack.contains(&fname) {
        Err(EvalException::Recursion(this.span, fname, new_stack))
    } else {
        let loc = { context.map.lock().unwrap().look_up_pos(this.span.low()) };
        new_stack.push(&fname, &descr, loc.file.name(), loc.position.line as u32);
        t(
            eval_expr(e, context)?.call(
                &new_stack,
                context.type_values.clone(),
                npos,
                nnamed,
                nargs,
                nkwargs,
            ),
            this,
        )
    }
}

fn eval_dot(
    this: &AstExpr,
    e: &AstExpr,
    s: &AstString,
    context: &mut EvaluationContext,
) -> EvalResult {
    let left = eval_expr(e, context)?;
    if let Some(v) = context.type_values.get_type_value(&left, &s.node) {
        if v.get_type() == "function" {
            // Insert self so the method see the object it is acting on
            Ok(function::Function::new_self_call(left.clone(), v))
        } else {
            Ok(v)
        }
    } else {
        t(left.get_attr(&s.node), this)
    }
}

fn eval_dict_comprehension(
    k: &AstExpr,
    v: &AstExpr,
    clauses: &[AstClause],
    context: &EvaluationContext,
) -> EvalResult {
    let mut r = Dictionary::new_typed();
    let tuple = Box::new(Spanned {
        span: k.span.merge(v.span),
        node: Expr::Tuple(vec![k.clone(), v.clone()]),
    });
    let mut context = context.child("dict_comprehension");
    for e in eval_comprehension_clause(&mut context, &tuple, clauses)? {
        let k = t(e.at(Value::from(0)), &tuple)?;
        let v = t(e.at(Value::from(1)), &tuple)?;
        t(r.set_at(k, v), &tuple)?;
    }
    Ok(Value::new(r))
}

fn eval_one_dimensional_comprehension(
    e: &AstExpr,
    clauses: &[AstClause],
    context: &EvaluationContext,
) -> Result<Vec<Value>, EvalException> {
    let mut r = Vec::new();
    let mut context = context.child("one_dimensional_comprehension");
    for v in eval_comprehension_clause(&mut context, e, clauses)? {
        r.push(v.clone());
    }
    Ok(r)
}

fn eval_list_comprehension(
    e: &AstExpr,
    clauses: &[AstClause],
    context: &EvaluationContext,
) -> EvalResult {
    eval_one_dimensional_comprehension(e, clauses, &context).map(Value::from)
}

enum TransformedExpr {
    Dot(Value, String, Span),
    ArrayIndirection(Value, Value, Span),
    List(Vec<TransformedExpr>, Span),
    Tuple(Vec<TransformedExpr>, Span),
    OtherExpr(AstExpr),
}

fn set_transformed(
    transformed: &TransformedExpr,
    context: &mut EvaluationContext,
    new_value: Value,
) -> EvalResult {
    let ok = Ok(Value::new(NoneType::None));
    match transformed {
        TransformedExpr::List(ref v, ref span) | &TransformedExpr::Tuple(ref v, ref span) => {
            let l = v.len() as i64;
            let nvl = t(new_value.length(), span)?;
            if nvl != l {
                Err(EvalException::IncorrectNumberOfValueToUnpack(*span, l, nvl))
            } else {
                let mut r = Vec::new();
                let mut it1 = v.iter();
                // TODO: the span here should probably include the rvalue
                let it2 = t(new_value.iter(), span)?;
                let mut it2 = it2.iter();
                for _ in 0..l {
                    r.push(set_transformed(
                        it1.next().unwrap(),
                        context,
                        it2.next().unwrap(),
                    )?)
                }
                ok
            }
        }
        TransformedExpr::Dot(ref e, ref s, ref span) => {
            t(e.clone().set_attr(&s, new_value), span)?;
            ok
        }
        TransformedExpr::ArrayIndirection(ref e, ref idx, ref span) => {
            t(e.clone().set_at(idx.clone(), new_value), span)?;
            ok
        }
        TransformedExpr::OtherExpr(ref e) => set_expr(e, context, new_value),
    }
}

fn eval_transformed(transformed: &TransformedExpr, context: &mut EvaluationContext) -> EvalResult {
    match transformed {
        TransformedExpr::Tuple(ref v, ..) => {
            let r = v
                .iter()
                .map(|i| eval_transformed(i, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::new(tuple::Tuple::new(r.as_slice())))
        }
        TransformedExpr::List(ref v, ..) => {
            let r = v
                .iter()
                .map(|i| eval_transformed(i, context))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Value::from(r))
        }
        TransformedExpr::Dot(ref left, ref s, ref span) => {
            if let Some(v) = context.type_values.get_type_value(left, &s) {
                if v.get_type() == "function" {
                    // Insert self so the method see the object it is acting on
                    Ok(function::Function::new_self_call(left.clone(), v))
                } else {
                    Ok(v)
                }
            } else {
                t(left.get_attr(&s), span)
            }
        }
        TransformedExpr::ArrayIndirection(ref e, ref idx, ref span) => t(e.at(idx.clone()), span),
        TransformedExpr::OtherExpr(ref e) => eval_expr(e, context),
    }
}

fn make_set(values: Vec<Value>, context: &EvaluationContext, span: Span) -> EvalResult {
    context
        .env
        .make_set(values)
        .map_err(|err| EvalException::DiagnosedError(err.to_diagnostic(span)))
}

// An intermediate transformation that tries to evaluate parameters of function / indices.
// It is used to cache result of LHS in augmented assignment.
// This transformation by default should be a deep copy (clone).
fn transform(
    expr: &AstExpr,
    context: &mut EvaluationContext,
) -> Result<TransformedExpr, EvalException> {
    match expr.node {
        Expr::Dot(ref e, ref s) => Ok(TransformedExpr::Dot(
            eval_expr(e, context)?,
            s.node.clone(),
            expr.span,
        )),
        Expr::ArrayIndirection(ref e, ref idx) => Ok(TransformedExpr::ArrayIndirection(
            eval_expr(e, context)?,
            eval_expr(idx, context)?,
            expr.span,
        )),
        Expr::List(ref v) => {
            let mut r = Vec::new();
            for val in v.iter() {
                r.push(transform(val, context)?)
            }
            Ok(TransformedExpr::List(r, expr.span))
        }
        Expr::Tuple(ref v) => {
            let mut r = Vec::new();
            for val in v.iter() {
                r.push(transform(val, context)?)
            }
            Ok(TransformedExpr::Tuple(r, expr.span))
        }
        _ => Ok(TransformedExpr::OtherExpr(expr.clone())),
    }
}

// Evaluate the AST element, i.e. mutate the environment and return an evaluation result
fn eval_expr(expr: &AstExpr, context: &mut EvaluationContext) -> EvalResult {
    match expr.node {
        Expr::Tuple(ref v) => {
            let r = eval_vector!(v, context);
            Ok(Value::new(tuple::Tuple::new(r.as_slice())))
        }
        Expr::Dot(ref e, ref s) => eval_dot(expr, e, s, context),
        Expr::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
            eval_call(expr, e, pos, named, args, kwargs, context)
        }
        Expr::ArrayIndirection(ref e, ref idx) => {
            let idx = eval_expr(idx, context)?;
            t(eval_expr(e, context)?.at(idx), expr)
        }
        Expr::Slice(ref a, ref start, ref stop, ref stride) => {
            eval_slice(expr, a, start, stop, stride, context)
        }
        Expr::Identifier(ref i) => t(context.env.get(&i.node), i),
        Expr::IntLiteral(ref i) => Ok(Value::new(i.node)),
        Expr::StringLiteral(ref s) => Ok(Value::new(s.node.clone())),
        Expr::Not(ref s) => Ok(Value::new(!eval_expr(s, context)?.to_bool())),
        Expr::Minus(ref s) => t(eval_expr(s, context)?.minus(), expr),
        Expr::Plus(ref s) => t(eval_expr(s, context)?.plus(), expr),
        Expr::Op(BinOp::Or, ref l, ref r) => {
            let l = eval_expr(l, context)?;
            Ok(if l.to_bool() {
                l
            } else {
                eval_expr(r, context)?
            })
        }
        Expr::Op(BinOp::And, ref l, ref r) => {
            let l = eval_expr(l, context)?;
            Ok(if !l.to_bool() {
                l
            } else {
                eval_expr(r, context)?
            })
        }
        Expr::Op(BinOp::EqualsTo, ref l, ref r) => eval_equals(expr, l, r, |x| x, context),
        Expr::Op(BinOp::Different, ref l, ref r) => eval_equals(expr, l, r, |x| !x, context),
        Expr::Op(BinOp::LowerThan, ref l, ref r) => {
            eval_compare(expr, l, r, |x| x == Ordering::Less, context)
        }
        Expr::Op(BinOp::GreaterThan, ref l, ref r) => {
            eval_compare(expr, l, r, |x| x == Ordering::Greater, context)
        }
        Expr::Op(BinOp::LowerOrEqual, ref l, ref r) => {
            eval_compare(expr, l, r, |x| x != Ordering::Greater, context)
        }
        Expr::Op(BinOp::GreaterOrEqual, ref l, ref r) => {
            eval_compare(expr, l, r, |x| x != Ordering::Less, context)
        }
        Expr::Op(BinOp::In, ref l, ref r) => t(
            eval_expr(r, context)?
                .is_in(&eval_expr(l, context)?)
                .map(Value::new),
            expr,
        ),
        Expr::Op(BinOp::NotIn, ref l, ref r) => t(
            eval_expr(r, context)?
                .is_in(&eval_expr(l, context)?)
                .map(|r| Value::new(!r)),
            expr,
        ),
        Expr::Op(BinOp::Substraction, ref l, ref r) => {
            t(eval_expr(l, context)?.sub(eval_expr(r, context)?), expr)
        }
        Expr::Op(BinOp::Addition, ref l, ref r) => {
            t(eval_expr(l, context)?.add(eval_expr(r, context)?), expr)
        }
        Expr::Op(BinOp::Multiplication, ref l, ref r) => {
            t(eval_expr(l, context)?.mul(eval_expr(r, context)?), expr)
        }
        Expr::Op(BinOp::Percent, ref l, ref r) => {
            t(eval_expr(l, context)?.percent(eval_expr(r, context)?), expr)
        }
        Expr::Op(BinOp::Division, ref l, ref r) => {
            let l = eval_expr(l, context)?;
            let r = eval_expr(r, context)?;
            // No types currently support / so always error.
            let err = ValueError::OperationNotSupported {
                op: "/".to_string(),
                left: l.get_type().to_string(),
                right: Some(r.get_type().to_string()),
            };
            Err(EvalException::DiagnosedError(err.to_diagnostic(expr.span)))
        }
        Expr::Op(BinOp::FloorDivision, ref l, ref r) => t(
            eval_expr(l, context)?.floor_div(eval_expr(r, context)?),
            expr,
        ),
        Expr::Op(BinOp::Pipe, ref l, ref r) => {
            t(eval_expr(l, context)?.pipe(eval_expr(r, context)?), expr)
        }
        Expr::If(ref cond, ref v1, ref v2) => {
            if eval_expr(cond, context)?.to_bool() {
                eval_expr(v1, context)
            } else {
                eval_expr(v2, context)
            }
        }
        Expr::List(ref v) => {
            let r = eval_vector!(v, context);
            Ok(Value::from(r))
        }
        Expr::Dict(ref v) => {
            let mut r = dict::Dictionary::new();
            for s in v.iter() {
                t(
                    r.set_at(eval_expr(&s.0, context)?, eval_expr(&s.1, context)?),
                    expr,
                )?
            }
            Ok(r)
        }
        Expr::Set(ref v) => {
            let values: Result<Vec<_>, _> = v.iter().map(|s| eval_expr(s, context)).collect();
            make_set(values?, context, expr.span)
        }
        Expr::ListComprehension(ref e, ref clauses) => eval_list_comprehension(e, clauses, context),
        Expr::DictComprehension((ref k, ref v), ref clauses) => {
            eval_dict_comprehension(k, v, clauses, context)
        }
        Expr::SetComprehension(ref e, ref clauses) => {
            let values = eval_one_dimensional_comprehension(e, clauses, context)?;
            make_set(values, context, expr.span)
        }
    }
}

// Perform an assignment on the LHS represented by this AST element
fn set_expr(expr: &AstExpr, context: &mut EvaluationContext, new_value: Value) -> EvalResult {
    let ok = Ok(Value::new(NoneType::None));
    match expr.node {
        Expr::Tuple(ref v) | Expr::List(ref v) => {
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
        Expr::Dot(ref e, ref s) => {
            t(eval_expr(e, context)?.set_attr(&(s.node), new_value), expr)?;
            ok
        }
        Expr::Identifier(ref i) => {
            t(context.env.set(&i.node, new_value), expr)?;
            ok
        }
        Expr::ArrayIndirection(ref e, ref idx) => {
            t(
                eval_expr(e, context)?.set_at(eval_expr(idx, context)?, new_value),
                expr,
            )?;
            ok
        }
        _ => Err(EvalException::IncorrectLeftValue(expr.span)),
    }
}

fn eval_assign_modify<F>(
    stmt: &AstStatement,
    lhs: &AstExpr,
    rhs: &AstExpr,
    context: &mut EvaluationContext,
    op: F,
) -> EvalResult
where
    F: FnOnce(&Value, Value) -> Result<Value, ValueError>,
{
    let lhs = transform(lhs, context)?;
    let l = eval_transformed(&lhs, context)?;
    let r = eval_expr(rhs, context)?;
    set_transformed(&lhs, context, t(op(&l, r), stmt)?)
}

fn eval_stmt(stmt: &AstStatement, context: &mut EvaluationContext) -> EvalResult {
    match stmt.node {
        Statement::Break => Err(EvalException::Break(stmt.span)),
        Statement::Continue => Err(EvalException::Continue(stmt.span)),
        Statement::Pass => Ok(Value::new(NoneType::None)),
        Statement::Return(Some(ref e)) => {
            Err(EvalException::Return(stmt.span, eval_expr(e, context)?))
        }
        Statement::Return(None) => {
            Err(EvalException::Return(stmt.span, Value::new(NoneType::None)))
        }
        Statement::Expression(ref e) => eval_expr(e, context),
        Statement::Assign(ref lhs, AssignOp::Assign, ref rhs) => {
            let rhs = eval_expr(rhs, context)?;
            set_expr(lhs, context, rhs)
        }
        Statement::Assign(ref lhs, AssignOp::Increment, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, Value::add)
        }
        Statement::Assign(ref lhs, AssignOp::Decrement, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, Value::sub)
        }
        Statement::Assign(ref lhs, AssignOp::Multiplier, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, Value::mul)
        }
        Statement::Assign(ref lhs, AssignOp::Divider, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, Value::div)
        }
        Statement::Assign(ref lhs, AssignOp::FloorDivider, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, Value::floor_div)
        }
        Statement::Assign(ref lhs, AssignOp::Percent, ref rhs) => {
            eval_assign_modify(stmt, lhs, rhs, context, Value::percent)
        }
        Statement::If(ref cond, ref st) => {
            if eval_expr(cond, context)?.to_bool() {
                eval_stmt(st, context)
            } else {
                Ok(Value::new(NoneType::None))
            }
        }
        Statement::IfElse(ref cond, ref st1, ref st2) => {
            if eval_expr(cond, context)?.to_bool() {
                eval_stmt(st1, context)
            } else {
                eval_stmt(st2, context)
            }
        }
        Statement::For(
            AstClause {
                ref span,
                node: Clause::For(ref e1, ref e2),
            },
            ref st,
        ) => {
            let mut iterable = eval_expr(e2, context)?;
            let mut result = Ok(Value::new(NoneType::None));
            iterable.freeze_for_iteration();
            for v in &t(iterable.iter(), span)? {
                set_expr(e1, context, v)?;
                match eval_stmt(st, context) {
                    Err(EvalException::Break(..)) => break,
                    Err(EvalException::Continue(..)) => (),
                    Err(x) => {
                        result = Err(x);
                        break;
                    }
                    _ => (),
                }
            }
            iterable.unfreeze_for_iteration();
            result
        }
        Statement::For(
            AstClause {
                span: ref _s,
                ref node,
            },
            ..
        ) => panic!("The parser returned an invalid for clause: {:?}", node),
        Statement::Def(ref name, ref params, ref stmts) => {
            let mut p = Vec::new();
            for x in params.iter() {
                p.push(match x.node {
                    Parameter::Normal(ref n) => FunctionParameter::Normal(n.node.clone()),
                    Parameter::WithDefaultValue(ref n, ref v) => {
                        FunctionParameter::WithDefaultValue(n.node.clone(), eval_expr(v, context)?)
                    }
                    Parameter::Args(ref n) => FunctionParameter::ArgsArray(n.node.clone()),
                    Parameter::KWArgs(ref n) => FunctionParameter::KWArgsDict(n.node.clone()),
                })
            }
            let f = function::Function::new_def(
                name.node.clone(),
                context.env.name(),
                p,
                stmts.clone(),
                context.map.clone(),
                context.env.assert_module_env().clone(),
            );
            t(context.env.set(&name.node, f.clone()), name)?;
            Ok(f)
        }
        Statement::Load(ref name, ref v) => {
            let loadenv = context.loader.load(name)?;
            for &(ref new_name, ref orig_name) in v.iter() {
                t(
                    context.env.assert_module_env().import_symbol(
                        &loadenv,
                        &orig_name.node,
                        &new_name.node,
                    ),
                    &new_name.span.merge(orig_name.span),
                )?
            }
            Ok(Value::new(NoneType::None))
        }
        Statement::Statements(ref v) => {
            let mut r = Value::new(NoneType::None);
            for stmt in v {
                r = eval_stmt(stmt, context)?;
            }
            Ok(r)
        }
    }
}

/// A method for consumption by def funcitons
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn eval_def(
    name: &str,
    call_stack: &CallStack,
    signature: &[FunctionParameter],
    stmts: &AstStatement,
    captured_env: Environment,
    type_values: TypeValues,
    args: Vec<FunctionArg>,
    map: Arc<Mutex<CodeMap>>,
) -> ValueResult {
    // argument binding
    let mut ctx = EvaluationContext {
        call_stack: call_stack.to_owned(),
        env: Rc::new(EvaluationContextEnvironment::Function(
            format!("{}#{}", captured_env.name(), name),
            captured_env,
            Default::default(),
        )),
        type_values,
        loader: Rc::new(UnreachableFileLoader),
        map: map.clone(),
    };

    let mut it2 = args.iter();
    for s in signature.iter() {
        match s {
            FunctionParameter::Normal(ref v)
            | FunctionParameter::WithDefaultValue(ref v, ..)
            | FunctionParameter::ArgsArray(ref v)
            | FunctionParameter::KWArgsDict(ref v) => {
                if let Err(x) = ctx.env.set(v, it2.next().unwrap().clone().into()) {
                    return Err(x.into());
                }
            }
            FunctionParameter::Optional(..) => {
                unreachable!("optional parameters only exist in native functions")
            }
        }
    }
    match eval_stmt(stmts, &mut ctx) {
        Err(EvalException::Return(_s, ret)) => Ok(ret),
        Err(x) => Err(ValueError::DiagnosedError(x.into())),
        Ok(..) => Ok(Value::new(NoneType::None)),
    }
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
#[allow(clippy::too_many_arguments)]
pub fn eval_lexer<
    T1: Iterator<Item = LexerItem>,
    T2: LexerIntoIter<T1>,
    T3: FileLoader + 'static,
>(
    map: &Arc<Mutex<CodeMap>>,
    filename: &str,
    content: &str,
    dialect: Dialect,
    lexer: T2,
    env: &mut Environment,
    type_values: TypeValues,
    file_loader: T3,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), type_values, file_loader, map.clone());
    match eval_stmt(
        &parse_lexer(map, filename, content, dialect, lexer)?,
        &mut context,
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
pub fn eval<T: FileLoader + 'static>(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    content: &str,
    build: Dialect,
    env: &mut Environment,
    type_values: TypeValues,
    file_loader: T,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), type_values, file_loader, map.clone());
    match eval_stmt(&parse(map, path, content, build)?, &mut context) {
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
pub fn eval_file<T: FileLoader + 'static>(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    build: Dialect,
    env: &mut Environment,
    type_values: TypeValues,
    file_loader: T,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), type_values, file_loader, map.clone());
    match eval_stmt(&parse_file(map, path, build)?, &mut context) {
        Ok(v) => Ok(v),
        Err(p) => Err(p.into()),
    }
}

pub mod interactive;
pub mod noload;
pub mod simple;

pub mod call_stack;

#[cfg(test)]
#[macro_use]
pub mod testutil;

#[cfg(test)]
mod tests;
