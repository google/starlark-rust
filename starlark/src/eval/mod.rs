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
use crate::eval::def::Def;
use crate::eval::stmt::AstStatementCompiled;
use crate::eval::stmt::BlockCompiled;
use crate::eval::stmt::StatementCompiled;
use crate::syntax::ast::*;
use crate::syntax::dialect::Dialect;
use crate::syntax::errors::SyntaxError;
use crate::syntax::lexer::{LexerIntoIter, LexerItem};
use crate::syntax::parser::{parse, parse_file, parse_lexer};
use crate::values::error::ValueError;
use crate::values::function::FunctionParameter;
use crate::values::function::FunctionSignature;
use crate::values::function::WrappedMethod;
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

fn eval_vector(v: &[AstExpr], ctx: &EvaluationContext) -> Result<Vec<Value>, EvalException> {
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
pub trait FileLoader: 'static {
    /// Open the file given by the load statement `path`.
    fn load(&self, path: &str) -> Result<Environment, EvalException>;
}

/// Starlark `def` or comprehension local variables
pub(crate) struct IndexedLocals<'a> {
    // name to index is needed for nested contexts only
    // (collection comprehensions).
    // TODO: access nested context objects by slot index too and drop this field
    name_to_index: &'a HashMap<String, usize>,
    /// locals store the local variable in an array. Each local variable loose its
    /// names and the `name_to_index` can be used to find a variable from name.
    /// Once the parsing of the `def` is finished, only the nested contexts should
    /// need it (the other one have been replaced during the parsing).
    /// `locals` is used to optimize access speed to local variable
    /// (versus looking into a hashmap).
    locals: RefCell<Vec<Option<Value>>>,
}

impl<'a> IndexedLocals<'a> {
    fn new(name_to_index: &'a HashMap<String, usize>) -> IndexedLocals<'a> {
        IndexedLocals {
            name_to_index,
            locals: RefCell::new(vec![None; name_to_index.len()]),
        }
    }

    fn get(&self, name: &str) -> Result<Option<Value>, EnvironmentError> {
        let slot = match self.name_to_index.get(name) {
            Some(slot) => *slot,
            None => return Ok(None),
        };
        Ok(Some(self.get_slot(slot, name)?))
    }

    fn get_slot(&self, slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        match self.locals.borrow()[slot].clone() {
            Some(value) => Ok(value),
            None => Err(EnvironmentError::LocalVariableReferencedBeforeAssignment(
                name.to_owned(),
            )),
        }
    }

    fn set(&self, name: &str, value: Value) {
        let slot = match self.name_to_index.get(name) {
            Some(slot) => *slot,
            None => panic!("unknown local: {}", name),
        };
        self.set_slot(slot, name, value);
    }

    fn set_slot(&self, slot: usize, _name: &str, value: Value) {
        self.locals.borrow_mut()[slot] = Some(value);
    }
}

/// Stacked environment for [`EvaluationContext`].
pub(crate) enum EvaluationContextEnvironment<'a> {
    /// Module-level
    Module(Environment, Rc<dyn FileLoader>),
    /// Function-level
    Function(Environment, IndexedLocals<'a>),
    /// Scope inside function, e. g. list comprenension
    Nested(&'a EvaluationContextEnvironment<'a>, IndexedLocals<'a>),
}

impl<'a> EvaluationContextEnvironment<'a> {
    fn env(&self) -> &Environment {
        match self {
            EvaluationContextEnvironment::Module(ref env, ..)
            | EvaluationContextEnvironment::Function(ref env, ..) => env,
            EvaluationContextEnvironment::Nested(ref parent, _) => parent.env(),
        }
    }

    fn make_set(&self, values: Vec<Value>) -> ValueResult {
        self.env().make_set(values)
    }

    fn loader(&self) -> Rc<dyn FileLoader> {
        match self {
            EvaluationContextEnvironment::Module(_, loader) => loader.clone(),
            _ => {
                // If we reach here, this is a bug.
                unreachable!()
            }
        }
    }

    fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        match self {
            EvaluationContextEnvironment::Module(env, ..) => env.get(name),
            EvaluationContextEnvironment::Function(env, locals) => match locals.get(name)? {
                Some(v) => Ok(v),
                None => env.get(name),
            },
            EvaluationContextEnvironment::Nested(parent, locals) => match locals.get(name)? {
                Some(v) => Ok(v),
                None => parent.get(name),
            },
        }
    }

    fn get_slot(&self, _slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        match self {
            EvaluationContextEnvironment::Function(_, locals)
            | EvaluationContextEnvironment::Nested(_, locals) => locals.get_slot(_slot, name),
            _ => unreachable!("slot in non-indexed environment"),
        }
    }

    fn set(&self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        match self {
            EvaluationContextEnvironment::Module(env, ..) => env.set(name, value),
            EvaluationContextEnvironment::Function(_, locals) => {
                locals.set(name, value);
                Ok(())
            }
            EvaluationContextEnvironment::Nested(_, locals) => {
                locals.set(name, value);
                Ok(())
            }
        }
    }

    fn set_slot(&self, slot: usize, name: &str, value: Value) {
        match self {
            EvaluationContextEnvironment::Function(_, locals)
            | EvaluationContextEnvironment::Nested(_, locals) => {
                locals.set_slot(slot, name, value);
            }
            _ => unreachable!("slot in non-indexed environment"),
        }
    }

    fn assert_module_env(&self) -> &Environment {
        match self {
            EvaluationContextEnvironment::Module(env, ..) => env,
            EvaluationContextEnvironment::Function(..)
            | EvaluationContextEnvironment::Nested(..) => {
                unreachable!("this function is meant to be called only on module level")
            }
        }
    }
}

/// A structure holding all the data about the evaluation context
/// (scope, load statement resolver, ...)
pub struct EvaluationContext<'a> {
    // Locals and captured context.
    env: EvaluationContextEnvironment<'a>,
    // Globals used to resolve type values, provided by the caller.
    type_values: TypeValues,
    call_stack: CallStack,
    map: Arc<Mutex<CodeMap>>,
}

impl<'a> EvaluationContext<'a> {
    fn new<T: FileLoader>(
        env: Environment,
        type_values: TypeValues,
        loader: T,
        map: Arc<Mutex<CodeMap>>,
    ) -> Self {
        EvaluationContext {
            call_stack: CallStack::default(),
            env: EvaluationContextEnvironment::Module(env, Rc::new(loader)),
            type_values,
            map,
        }
    }

    fn child(&'a self, name_to_index: &'a HashMap<String, usize>) -> EvaluationContext<'a> {
        EvaluationContext {
            env: EvaluationContextEnvironment::Nested(&self.env, IndexedLocals::new(name_to_index)),
            type_values: self.type_values.clone(),
            call_stack: self.call_stack.clone(),
            map: self.map.clone(),
        }
    }
}

fn eval_compare<F>(
    this: &AstExpr,
    left: &AstExpr,
    right: &AstExpr,
    cmp: F,
    context: &EvaluationContext,
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
    context: &EvaluationContext,
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

fn eval_slice<'a>(
    this: &AstExpr,
    a: &AstExpr,
    start: &Option<AstExpr>,
    stop: &Option<AstExpr>,
    stride: &Option<AstExpr>,
    context: &EvaluationContext,
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

fn eval_call<'a>(
    this: &AstExpr,
    e: &AstExpr,
    pos: &[AstExpr],
    named: &[(AstString, AstExpr)],
    args: &Option<AstExpr>,
    kwargs: &Option<AstExpr>,
    context: &EvaluationContext,
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
    let mut new_stack = context.call_stack.clone();
    if context.call_stack.contains(f.function_id()) {
        Err(EvalException::Recursion(this.span, f.to_repr(), new_stack))
    } else {
        new_stack.push(f.clone(), context.map.clone(), this.span.low());
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

fn eval_dot<'a>(
    this: &AstExpr,
    e: &AstExpr,
    s: &AstString,
    context: &EvaluationContext,
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
    Identifier(AstString),
    Slot(usize, AstString),
}

fn set_transformed<'a>(
    transformed: &TransformedExpr,
    context: &EvaluationContext,
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
        TransformedExpr::Identifier(ident) => {
            t(context.env.set(&ident.node, new_value), ident)?;
            ok
        }
        TransformedExpr::Slot(slot, ident) => {
            context.env.set_slot(*slot, &ident.node, new_value);
            ok
        }
    }
}

fn eval_transformed<'a>(transformed: &TransformedExpr, context: &EvaluationContext) -> EvalResult {
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
        TransformedExpr::Identifier(ident) => t(context.env.get(&ident.node), ident),
        TransformedExpr::Slot(slot, ident) => t(context.env.get_slot(*slot, &ident.node), ident),
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
    expr: &AstAugmentedAssignTargetExpr,
    context: &EvaluationContext,
) -> Result<TransformedExpr, EvalException> {
    match expr.node {
        AugmentedAssignTargetExpr::Dot(ref e, ref s) => Ok(TransformedExpr::Dot(
            eval_expr(e, context)?,
            s.node.clone(),
            expr.span,
        )),
        AugmentedAssignTargetExpr::ArrayIndirection(ref e, ref idx) => {
            Ok(TransformedExpr::ArrayIndirection(
                eval_expr(e, context)?,
                eval_expr(idx, context)?,
                expr.span,
            ))
        }
        AugmentedAssignTargetExpr::Slot(index, ref ident) => {
            Ok(TransformedExpr::Slot(index, ident.clone()))
        }
        AugmentedAssignTargetExpr::Identifier(ref ident) => {
            Ok(TransformedExpr::Identifier(ident.clone()))
        }
    }
}

// Evaluate the AST element, i.e. mutate the environment and return an evaluation result
fn eval_expr(expr: &AstExpr, context: &EvaluationContext) -> EvalResult {
    match expr.node {
        Expr::Tuple(ref v) => {
            let r = eval_vector(v, context)?;
            Ok(Value::new(tuple::Tuple::new(r)))
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
        Expr::Slot(slot, ref i) => t(context.env.get_slot(slot, &i.node), i),
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
            let r = eval_vector(v, context)?;
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
            let mut values = Vec::with_capacity(v.len());
            for s in v {
                values.push(eval_expr(s, context)?);
            }
            make_set(values, context, expr.span)
        }
        Expr::ListComprehension(..) | Expr::DictComprehension(..) | Expr::SetComprehension(..) => {
            unreachable!()
        }
        Expr::ComprehensionCompiled(ref e) => e.eval(expr.span, context),
    }
}

// Perform an assignment on the LHS represented by this AST element
fn set_expr(
    expr: &AstAssignTargetExpr,
    context: &EvaluationContext,
    new_value: Value,
) -> EvalResult {
    let ok = Ok(Value::new(NoneType::None));
    match expr.node {
        AssignTargetExpr::Subtargets(ref v) => {
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
        AssignTargetExpr::Dot(ref e, ref s) => {
            t(eval_expr(e, context)?.set_attr(&(s.node), new_value), expr)?;
            ok
        }
        AssignTargetExpr::Identifier(ref i) => {
            t(context.env.set(&i.node, new_value), expr)?;
            ok
        }
        AssignTargetExpr::Slot(slot, ref i) => {
            context.env.set_slot(slot, &i.node, new_value);
            ok
        }
        AssignTargetExpr::ArrayIndirection(ref e, ref idx) => {
            t(
                eval_expr(e, context)?.set_at(eval_expr(idx, context)?, new_value),
                expr,
            )?;
            ok
        }
    }
}

fn eval_assign_modify(
    stmt: &AstStatementCompiled,
    lhs: &AstAugmentedAssignTargetExpr,
    rhs: &AstExpr,
    context: &EvaluationContext,
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

fn eval_stmt(stmt: &AstStatementCompiled, context: &EvaluationContext) -> EvalResult {
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
            let mut iterable = eval_expr(e2, context)?;
            let mut result = Ok(Value::new(NoneType::None));
            iterable.freeze_for_iteration();
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
            iterable.unfreeze_for_iteration();
            result
        }
        StatementCompiled::Def(ref stmt) => {
            let mut p = Vec::new();
            for x in &stmt.params {
                p.push(match x.node {
                    Parameter::Normal(ref n) => FunctionParameter::Normal(n.node.clone()),
                    Parameter::WithDefaultValue(ref n, ref v) => {
                        FunctionParameter::WithDefaultValue(n.node.clone(), eval_expr(v, context)?)
                    }
                    Parameter::Args(ref n) => FunctionParameter::ArgsArray(n.node.clone()),
                    Parameter::KWArgs(ref n) => FunctionParameter::KWArgsDict(n.node.clone()),
                })
            }
            let f = Def::new(
                context.env.assert_module_env().name(),
                FunctionSignature::new(p, 0),
                stmt.clone(),
                context.map.clone(),
                context.env.assert_module_env().clone(),
            );
            t(context.env.set(&stmt.name.node, f.clone()), &stmt.name)?;
            Ok(f)
        }
        StatementCompiled::Load(ref name, ref v) => {
            let loadenv = context.env.loader().load(name)?;
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
    }
}

fn eval_block(block: &BlockCompiled, context: &EvaluationContext) -> EvalResult {
    let mut r = Value::new(NoneType::None);
    for stmt in &block.0 {
        r = eval_stmt(stmt, context)?;
    }
    Ok(r)
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
    let context = EvaluationContext::new(env.clone(), type_values, file_loader, map.clone());
    match eval_block(
        &parse_lexer(map, filename, content, dialect, lexer)?,
        &context,
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
    let context = EvaluationContext::new(env.clone(), type_values, file_loader, map.clone());
    match eval_block(&parse(map, path, content, build)?, &context) {
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
    let context = EvaluationContext::new(env.clone(), type_values, file_loader, map.clone());
    match eval_block(&parse_file(map, path, build)?, &context) {
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

pub(crate) mod compr;
pub(crate) mod def;
pub mod stmt;
