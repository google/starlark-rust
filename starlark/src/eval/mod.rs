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
use crate::eval::call_stack::CallStack;
use crate::syntax::ast::*;
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
use std::cmp::Ordering;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

macro_rules! eval_vector {
    ($v:expr, $ctx:expr) => {{
        let mut r = Vec::new();
        for s in $v.iter() {
            r.push(s.eval($ctx)?)
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

type EvalResult = Result<Value, EvalException>;

macro_rules! t {
    ($v:expr,span $el:expr) => {{
        match $v {
            Err(e) => Err(EvalException::DiagnosedError(e.to_diagnostic($el))),
            Ok(v) => Ok(v),
        }
    }};
    ($v:expr, $el:expr) => {{
        match $v {
            Err(e) => Err(EvalException::DiagnosedError(e.to_diagnostic($el.span))),
            Ok(v) => Ok(v),
        }
    }};
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

/// A structure holding all the data about the evaluation context
/// (scope, load statement resolver, ...)
pub struct EvaluationContext {
    // Locals and captured context.
    env: Environment,
    // Globals used to resolve types (e. g. set constructor)
    // this is provider by caller.
    globals: Environment,
    loader: Rc<dyn FileLoader>,
    call_stack: CallStack,
    map: Arc<Mutex<CodeMap>>,
}

impl EvaluationContext {
    fn new<T: FileLoader>(
        env: Environment,
        globals: Environment,
        loader: T,
        map: Arc<Mutex<CodeMap>>,
    ) -> Self {
        EvaluationContext {
            call_stack: CallStack::default(),
            env,
            globals,
            loader: Rc::new(loader),
            map,
        }
    }

    fn child(&self, name: &str) -> EvaluationContext {
        EvaluationContext {
            env: self.env.child(name),
            globals: self.globals.clone(),
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

// A trait to add an eval function to the AST elements
trait Evaluate {
    // Evaluate the AST element, i.e. mutate the environment and return an evaluation result
    fn eval(&self, context: &mut EvaluationContext) -> EvalResult;

    // An intermediate transformation that tries to evaluate parameters of function / indices.
    // It is used to cache result of LHS in augmented assignment.
    // This transformation by default should be a deep copy (clone).
    fn transform(
        &self,
        context: &mut EvaluationContext,
    ) -> Result<Box<dyn Evaluate>, EvalException>;

    // Perform an assignment on the LHS represented by this AST element
    fn set(&self, context: &mut EvaluationContext, new_value: Value) -> EvalResult;
}

impl Evaluate for AstString {
    fn eval(&self, _context: &mut EvaluationContext) -> EvalResult {
        Ok(Value::new(self.node.clone()))
    }

    fn transform(
        &self,
        _context: &mut EvaluationContext,
    ) -> Result<Box<dyn Evaluate>, EvalException> {
        Ok(Box::new(self.clone()))
    }

    fn set(&self, _context: &mut EvaluationContext, _new_value: Value) -> EvalResult {
        Err(EvalException::IncorrectLeftValue(self.span))
    }
}

impl Evaluate for AstInt {
    fn eval(&self, _context: &mut EvaluationContext) -> EvalResult {
        Ok(Value::new(self.node))
    }

    fn transform(
        &self,
        _context: &mut EvaluationContext,
    ) -> Result<Box<dyn Evaluate>, EvalException> {
        Ok(Box::new(*self))
    }

    fn set(&self, _context: &mut EvaluationContext, _new_value: Value) -> EvalResult {
        Err(EvalException::IncorrectLeftValue(self.span))
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
                if cond.eval(context)?.to_bool() {
                    if tl.is_empty() {
                        result.push(e.eval(context)?);
                    } else {
                        let mut other = eval_comprehension_clause(context, e, tl)?;
                        result.append(&mut other);
                    }
                };
            }
            Clause::For(ref k, ref v) => {
                let mut iterable = v.eval(context)?;
                iterable.freeze_for_iteration();
                for i in &t!(iterable.iter(), c)? {
                    k.set(context, i)?;
                    if tl.is_empty() {
                        result.push(e.eval(context)?);
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
    let l = left.eval(context)?;
    let r = right.eval(context)?;
    Ok(Value::new(cmp(t!(l.compare(&r), this)?)))
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
    let l = left.eval(context)?;
    let r = right.eval(context)?;
    Ok(Value::new(cmp(t!(
        l.equals(&r).map_err(Into::<ValueError>::into),
        this
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
    let a = a.eval(context)?;
    let start = match start {
        Some(ref e) => Some(e.eval(context)?),
        None => None,
    };
    let stop = match stop {
        Some(ref e) => Some(e.eval(context)?),
        None => None,
    };
    let stride = match stride {
        Some(ref e) => Some(e.eval(context)?),
        None => None,
    };
    t!(a.slice(start, stop, stride), this)
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
        nnamed.insert(k.eval(context)?.to_str(), v.eval(context)?);
    }
    let nargs = if let Some(ref x) = args {
        Some(x.eval(context)?)
    } else {
        None
    };
    let nkwargs = if let Some(ref x) = kwargs {
        Some(x.eval(context)?)
    } else {
        None
    };
    let f = e.eval(context)?;
    let fname = f.to_repr();
    let descr = f.to_str();
    let mut new_stack = context.call_stack.clone();
    if context.call_stack.contains(&fname) {
        Err(EvalException::Recursion(this.span, fname, new_stack))
    } else {
        let loc = { context.map.lock().unwrap().look_up_pos(this.span.low()) };
        new_stack.push(&fname, &descr, loc.file.name(), loc.position.line as u32);
        t!(
            e.eval(context,)?.call(
                &new_stack,
                context.globals.clone(),
                npos,
                nnamed,
                nargs,
                nkwargs,
            ),
            this
        )
    }
}

fn eval_dot(
    this: &AstExpr,
    e: &AstExpr,
    s: &AstString,
    context: &mut EvaluationContext,
) -> EvalResult {
    let left = e.eval(context)?;
    if let Some(v) = context.env.get_type_value(&left, &s.node) {
        if v.get_type() == "function" {
            // Insert self so the method see the object it is acting on
            Ok(function::Function::new_self_call(left.clone(), v))
        } else {
            Ok(v)
        }
    } else {
        t!(left.get_attr(&s.node), this)
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
        let k = t!(e.at(Value::from(0)), tuple)?;
        let v = t!(e.at(Value::from(1)), tuple)?;
        t!(r.set_at(k, v), tuple)?;
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
    List(Vec<Box<dyn Evaluate>>, Span),
    Tuple(Vec<Box<dyn Evaluate>>, Span),
}

impl Evaluate for TransformedExpr {
    fn transform(
        &self,
        _context: &mut EvaluationContext,
    ) -> Result<Box<dyn Evaluate>, EvalException> {
        panic!("Transform should not be called on an already transformed object");
    }

    fn set(&self, context: &mut EvaluationContext, new_value: Value) -> EvalResult {
        let ok = Ok(Value::new(NoneType::None));
        match self {
            TransformedExpr::List(ref v, ref span) | &TransformedExpr::Tuple(ref v, ref span) => {
                let l = v.len() as i64;
                let nvl = t!(new_value.length(), span * span)?;
                if nvl != l {
                    Err(EvalException::IncorrectNumberOfValueToUnpack(*span, l, nvl))
                } else {
                    let mut r = Vec::new();
                    let mut it1 = v.iter();
                    // TODO: the span here should probably include the rvalue
                    let it2 = t!(new_value.iter(), span * span)?;
                    let mut it2 = it2.iter();
                    for _ in 0..l {
                        r.push(it1.next().unwrap().set(context, it2.next().unwrap())?)
                    }
                    ok
                }
            }
            TransformedExpr::Dot(ref e, ref s, ref span) => {
                t!(e.clone().set_attr(&s, new_value), span * span)?;
                ok
            }
            TransformedExpr::ArrayIndirection(ref e, ref idx, ref span) => {
                t!(e.clone().set_at(idx.clone(), new_value), span * span)?;
                ok
            }
        }
    }

    fn eval(&self, context: &mut EvaluationContext) -> EvalResult {
        match self {
            TransformedExpr::Tuple(ref v, ..) => {
                let r = eval_vector!(v, context);
                Ok(Value::new(tuple::Tuple::new(r.as_slice())))
            }
            TransformedExpr::List(ref v, ..) => {
                let r = eval_vector!(v, context);
                Ok(Value::from(r))
            }
            TransformedExpr::Dot(ref left, ref s, ref span) => {
                if let Some(v) = context.env.get_type_value(left, &s) {
                    if v.get_type() == "function" {
                        // Insert self so the method see the object it is acting on
                        Ok(function::Function::new_self_call(left.clone(), v))
                    } else {
                        Ok(v)
                    }
                } else {
                    t!(left.get_attr(&s), span span.clone())
                }
            }
            TransformedExpr::ArrayIndirection(ref e, ref idx, ref span) => {
                t!(e.at(idx.clone()), span span.clone())
            }
        }
    }
}

fn make_set(values: Vec<Value>, context: &EvaluationContext, span: Span) -> EvalResult {
    context
        .env
        .make_set(values)
        .map_err(|err| EvalException::DiagnosedError(err.to_diagnostic(span)))
}

impl Evaluate for AstExpr {
    fn transform(
        &self,
        context: &mut EvaluationContext,
    ) -> Result<Box<dyn Evaluate>, EvalException> {
        match self.node {
            Expr::Dot(ref e, ref s) => Ok(Box::new(TransformedExpr::Dot(
                e.eval(context)?,
                s.node.clone(),
                self.span,
            ))),
            Expr::ArrayIndirection(ref e, ref idx) => Ok(Box::new(
                TransformedExpr::ArrayIndirection(e.eval(context)?, idx.eval(context)?, self.span),
            )),
            Expr::List(ref v) => {
                let mut r = Vec::new();
                for val in v.iter() {
                    r.push(val.transform(context)?)
                }
                Ok(Box::new(TransformedExpr::List(r, self.span)))
            }
            Expr::Tuple(ref v) => {
                let mut r = Vec::new();
                for val in v.iter() {
                    r.push(val.transform(context)?)
                }
                Ok(Box::new(TransformedExpr::Tuple(r, self.span)))
            }
            _ => Ok(Box::new(self.clone())),
        }
    }

    #[allow(unconditional_recursion)]
    fn eval(&self, context: &mut EvaluationContext) -> EvalResult {
        match self.node {
            Expr::Tuple(ref v) => {
                let r = eval_vector!(v, context);
                Ok(Value::new(tuple::Tuple::new(r.as_slice())))
            }
            Expr::Dot(ref e, ref s) => eval_dot(self, e, s, context),
            Expr::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
                eval_call(self, e, pos, named, args, kwargs, context)
            }
            Expr::ArrayIndirection(ref e, ref idx) => {
                let idx = idx.eval(context)?;
                t!(e.eval(context)?.at(idx), self)
            }
            Expr::Slice(ref a, ref start, ref stop, ref stride) => {
                eval_slice(self, a, start, stop, stride, context)
            }
            Expr::Identifier(ref i) => t!(context.env.get(&i.node), i),
            Expr::IntLiteral(ref i) => Ok(Value::new(i.node)),
            Expr::StringLiteral(ref s) => Ok(Value::new(s.node.clone())),
            Expr::Not(ref s) => Ok(Value::new(!s.eval(context)?.to_bool())),
            Expr::Minus(ref s) => t!(s.eval(context)?.minus(), self),
            Expr::Plus(ref s) => t!(s.eval(context)?.plus(), self),
            Expr::Op(BinOp::Or, ref l, ref r) => {
                let l = l.eval(context)?;
                Ok(if l.to_bool() { l } else { r.eval(context)? })
            }
            Expr::Op(BinOp::And, ref l, ref r) => {
                let l = l.eval(context)?;
                Ok(if !l.to_bool() { l } else { r.eval(context)? })
            }
            Expr::Op(BinOp::EqualsTo, ref l, ref r) => eval_equals(self, l, r, |x| x, context),
            Expr::Op(BinOp::Different, ref l, ref r) => eval_equals(self, l, r, |x| !x, context),
            Expr::Op(BinOp::LowerThan, ref l, ref r) => {
                eval_compare(self, l, r, |x| x == Ordering::Less, context)
            }
            Expr::Op(BinOp::GreaterThan, ref l, ref r) => {
                eval_compare(self, l, r, |x| x == Ordering::Greater, context)
            }
            Expr::Op(BinOp::LowerOrEqual, ref l, ref r) => {
                eval_compare(self, l, r, |x| x != Ordering::Greater, context)
            }
            Expr::Op(BinOp::GreaterOrEqual, ref l, ref r) => {
                eval_compare(self, l, r, |x| x != Ordering::Less, context)
            }
            Expr::Op(BinOp::In, ref l, ref r) => t!(
                r.eval(context)?.is_in(&l.eval(context)?).map(Value::new),
                self
            ),
            Expr::Op(BinOp::NotIn, ref l, ref r) => t!(
                r.eval(context)?
                    .is_in(&l.eval(context)?)
                    .map(|r| Value::new(!r)),
                self
            ),
            Expr::Op(BinOp::Substraction, ref l, ref r) => {
                t!(l.eval(context)?.sub(r.eval(context)?), self)
            }
            Expr::Op(BinOp::Addition, ref l, ref r) => {
                t!(l.eval(context)?.add(r.eval(context)?), self)
            }
            Expr::Op(BinOp::Multiplication, ref l, ref r) => {
                t!(l.eval(context)?.mul(r.eval(context)?), self)
            }
            Expr::Op(BinOp::Percent, ref l, ref r) => {
                t!(l.eval(context)?.percent(r.eval(context)?), self)
            }
            Expr::Op(BinOp::Division, ref l, ref r) => {
                let l = l.eval(context)?;
                let r = r.eval(context)?;
                // No types currently support / so always error.
                let err = ValueError::OperationNotSupported {
                    op: "/".to_string(),
                    left: l.get_type().to_string(),
                    right: Some(r.get_type().to_string()),
                };
                Err(EvalException::DiagnosedError(err.to_diagnostic(self.span)))
            }
            Expr::Op(BinOp::FloorDivision, ref l, ref r) => {
                t!(l.eval(context)?.floor_div(r.eval(context)?), self)
            }
            Expr::Op(BinOp::Pipe, ref l, ref r) => {
                t!(l.eval(context)?.pipe(r.eval(context)?), self)
            }
            Expr::If(ref cond, ref v1, ref v2) => {
                if cond.eval(context)?.to_bool() {
                    v1.eval(context)
                } else {
                    v2.eval(context)
                }
            }
            Expr::List(ref v) => {
                let r = eval_vector!(v, context);
                Ok(Value::from(r))
            }
            Expr::Dict(ref v) => {
                let mut r = dict::Dictionary::new();
                for s in v.iter() {
                    t!(r.set_at(s.0.eval(context)?, s.1.eval(context)?), self)?
                }
                Ok(r)
            }
            Expr::Set(ref v) => {
                let values: Result<Vec<_>, _> = v.iter().map(|s| s.eval(context)).collect();
                make_set(values?, context, self.span)
            }
            Expr::ListComprehension(ref e, ref clauses) => {
                eval_list_comprehension(e, clauses, context)
            }
            Expr::DictComprehension((ref k, ref v), ref clauses) => {
                eval_dict_comprehension(k, v, clauses, context)
            }
            Expr::SetComprehension(ref e, ref clauses) => {
                let values = eval_one_dimensional_comprehension(e, clauses, context)?;
                make_set(values, context, self.span)
            }
        }
    }

    fn set(&self, context: &mut EvaluationContext, new_value: Value) -> EvalResult {
        let ok = Ok(Value::new(NoneType::None));
        match self.node {
            Expr::Tuple(ref v) | Expr::List(ref v) => {
                // TODO: the span here should probably include the rvalue
                let new_values: Vec<Value> = t!(new_value.iter(), self)?.iter().collect();
                let l = v.len();
                if new_values.len() != l {
                    Err(EvalException::IncorrectNumberOfValueToUnpack(
                        self.span,
                        l as i64,
                        new_values.len() as i64,
                    ))
                } else {
                    let mut it1 = v.iter();
                    let mut it2 = new_values.into_iter();
                    for _ in 0..l {
                        it1.next().unwrap().set(context, it2.next().unwrap())?;
                    }
                    ok
                }
            }
            Expr::Dot(ref e, ref s) => {
                t!(e.eval(context)?.set_attr(&(s.node), new_value), self)?;
                ok
            }
            Expr::Identifier(ref i) => {
                t!(context.env.set(&i.node, new_value), self)?;
                ok
            }
            Expr::ArrayIndirection(ref e, ref idx) => {
                t!(e.eval(context)?.set_at(idx.eval(context)?, new_value), self)?;
                ok
            }
            _ => Err(EvalException::IncorrectLeftValue(self.span)),
        }
    }
}

impl Evaluate for AstStatement {
    fn eval(&self, context: &mut EvaluationContext) -> EvalResult {
        match self.node {
            Statement::Break => Err(EvalException::Break(self.span)),
            Statement::Continue => Err(EvalException::Continue(self.span)),
            Statement::Pass => Ok(Value::new(NoneType::None)),
            Statement::Return(Some(ref e)) => {
                Err(EvalException::Return(self.span, e.eval(context)?))
            }
            Statement::Return(None) => {
                Err(EvalException::Return(self.span, Value::new(NoneType::None)))
            }
            Statement::Expression(ref e) => e.eval(context),
            Statement::Assign(ref lhs, AssignOp::Assign, ref rhs) => {
                let rhs = rhs.eval(context)?;
                lhs.set(context, rhs)
            }
            Statement::Assign(ref lhs, AssignOp::Increment, ref rhs) => {
                let lhs = lhs.transform(context)?;
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.add(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Decrement, ref rhs) => {
                let lhs = lhs.transform(context)?;
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.sub(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Multiplier, ref rhs) => {
                let lhs = lhs.transform(context)?;
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.mul(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Divider, ref rhs) => {
                let lhs = lhs.transform(context)?;
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.div(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::FloorDivider, ref rhs) => {
                let lhs = lhs.transform(context)?;
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.floor_div(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Percent, ref rhs) => {
                let lhs = lhs.transform(context)?;
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.percent(r), self)?)
            }
            Statement::If(ref cond, ref st) => {
                if cond.eval(context)?.to_bool() {
                    st.eval(context)
                } else {
                    Ok(Value::new(NoneType::None))
                }
            }
            Statement::IfElse(ref cond, ref st1, ref st2) => {
                if cond.eval(context)?.to_bool() {
                    st1.eval(context)
                } else {
                    st2.eval(context)
                }
            }
            Statement::For(
                AstClause {
                    ref span,
                    node: Clause::For(ref e1, ref e2),
                },
                ref st,
            ) => {
                let mut iterable = e2.eval(context)?;
                let mut result = Ok(Value::new(NoneType::None));
                iterable.freeze_for_iteration();
                for v in &t!(iterable.iter(), span * span)? {
                    e1.set(context, v)?;
                    match st.eval(context) {
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
                            FunctionParameter::WithDefaultValue(n.node.clone(), v.eval(context)?)
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
                    context.env.clone(),
                );
                t!(context.env.set(&name.node, f.clone()), name)?;
                Ok(f)
            }
            Statement::Load(ref name, ref v) => {
                let loadenv = context.loader.load(name)?;
                for &(ref new_name, ref orig_name) in v.iter() {
                    t!(context.env.import_symbol(&loadenv, &orig_name.node, &new_name.node),
                        span new_name.span.merge(orig_name.span))?
                }
                Ok(Value::new(NoneType::None))
            }
            Statement::Statements(ref v) => {
                let r = eval_vector!(v, context);
                match r.len() {
                    0 => Ok(Value::new(NoneType::None)),
                    _ => Ok(r.last().unwrap().clone()),
                }
            }
        }
    }

    fn transform(
        &self,
        _context: &mut EvaluationContext,
    ) -> Result<Box<dyn Evaluate>, EvalException> {
        Ok(Box::new(self.clone()))
    }

    fn set(&self, _context: &mut EvaluationContext, _new_value: Value) -> EvalResult {
        Err(EvalException::IncorrectLeftValue(self.span))
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
    globals: Environment,
    args: Vec<FunctionArg>,
    map: Arc<Mutex<CodeMap>>,
) -> ValueResult {
    // argument binding
    let env = captured_env.child(&format!("{}#{}", captured_env.name(), name));

    let mut it2 = args.iter();
    for s in signature.iter() {
        match s {
            FunctionParameter::Normal(ref v)
            | FunctionParameter::WithDefaultValue(ref v, ..)
            | FunctionParameter::ArgsArray(ref v)
            | FunctionParameter::KWArgsDict(ref v) => {
                if let Err(x) = env.set(v, it2.next().unwrap().clone().into()) {
                    return Err(x.into());
                }
            }
            FunctionParameter::Optional(..) => {
                unreachable!("optional parameters only exist in native functions")
            }
        }
    }
    let mut ctx = EvaluationContext {
        call_stack: call_stack.to_owned(),
        env,
        globals,
        loader: Rc::new(UnreachableFileLoader),
        map: map.clone(),
    };
    match stmts.eval(&mut ctx) {
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
/// * file_loader: the [FileLoader](trait.FileLoader.html) to react to `load()` statements.
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
    globals: Environment,
    file_loader: T3,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), globals, file_loader, map.clone());
    match parse_lexer(map, filename, content, dialect, lexer)?.eval(&mut context) {
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
/// * file_loader: the [FileLoader](trait.FileLoader.html) to react to `load()` statements.
pub fn eval<T: FileLoader + 'static>(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    content: &str,
    build: Dialect,
    env: &mut Environment,
    globals: Environment,
    file_loader: T,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), globals, file_loader, map.clone());
    match parse(map, path, content, build)?.eval(&mut context) {
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
/// * file_loader: the [FileLoader](trait.FileLoader.html) to react to `load()` statements.
pub fn eval_file<T: FileLoader + 'static>(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    build: Dialect,
    env: &mut Environment,
    globals: Environment,
    file_loader: T,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), globals, file_loader, map.clone());
    match parse_file(map, path, build)?.eval(&mut context) {
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
