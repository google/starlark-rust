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

//! Evaluation environment, provide converters from Ast* element to value
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use syntax::ast::*;
use syntax::errors::SyntaxError;
use syntax::parser::{parse_file, parse_lexer, parse};
use syntax::lexer::{LexerIntoIter, LexerItem};
use values::*;
use environment::Environment;
use values::function::FunctionParameter;
use codemap::{CodeMap, Span, Spanned};
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use linked_hash_map::LinkedHashMap;

macro_rules! eval_vector {
    ($v: expr, $ctx: expr) => {
        {
            let mut r = Vec::new();
            for s in $v.iter() {
                r.push(s.eval($ctx)?)
            }
            r
        }
    }
}

// TODO: move that code in some common error code list?
// CE prefix = Critical Evaluation
#[doc(hidden)]
pub const BREAK_ERROR_CODE: &'static str = "CE00";
#[doc(hidden)]
pub const CONTINUE_ERROR_CODE: &'static str = "CE01";
#[doc(hidden)]
pub const RETURN_ERROR_CODE: &'static str = "CE02";
#[doc(hidden)]
pub const INCORRECT_LEFT_VALUE_ERROR_CODE: &'static str = "CE03";
#[doc(hidden)]
pub const INCORRECT_UNPACK_ERROR_CODE: &'static str = "CE04";
#[doc(hidden)]
pub const RECURSION_ERROR_CODE: &'static str = "CE05";

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
    Recursion(Span, String, Vec<String>),
}

type EvalResult = Result<Value, EvalException>;

macro_rules! t {
    ($v: expr, span $el: expr) => {
        {
            match $v {
                Err(e) => Err(EvalException::DiagnosedError(e.to_diagnostic($el))),
                Ok(v) => Ok(v)
            }
        }
    };
    ($v: expr, $el: expr) => {
        {
            match $v {
                Err(e) => Err(EvalException::DiagnosedError(e.to_diagnostic($el.span))),
                Ok(v) => Ok(v)
            }
        }
    };
}

impl Into<Diagnostic> for EvalException {
    fn into(self) -> Diagnostic {
        match self {
            EvalException::DiagnosedError(e) => e,
            EvalException::Break(s) => {
                Diagnostic {
                    level: Level::Error,
                    message: "Break statement used outside of a loop".to_owned(),
                    code: Some(BREAK_ERROR_CODE.to_owned()),
                    spans: vec![
                        SpanLabel {
                            span: s,
                            style: SpanStyle::Primary,
                            label: None,
                        },
                    ],
                }
            }
            EvalException::Continue(s) => {
                Diagnostic {
                    level: Level::Error,
                    message: "Continue statement used outside of a loop".to_owned(),
                    code: Some(CONTINUE_ERROR_CODE.to_owned()),
                    spans: vec![
                        SpanLabel {
                            span: s,
                            style: SpanStyle::Primary,
                            label: None,
                        },
                    ],
                }
            }
            EvalException::Return(s, ..) => {
                Diagnostic {
                    level: Level::Error,
                    message: "Return statement used outside of a function call".to_owned(),
                    code: Some(RETURN_ERROR_CODE.to_owned()),
                    spans: vec![
                        SpanLabel {
                            span: s,
                            style: SpanStyle::Primary,
                            label: None,
                        },
                    ],
                }
            }
            EvalException::IncorrectLeftValue(s) => {
                Diagnostic {
                    level: Level::Error,
                    message: "Incorrect expression as left value".to_owned(),
                    code: Some(INCORRECT_LEFT_VALUE_ERROR_CODE.to_owned()),
                    spans: vec![
                        SpanLabel {
                            span: s,
                            style: SpanStyle::Primary,
                            label: None,
                        },
                    ],
                }
            }
            EvalException::IncorrectNumberOfValueToUnpack(s, expected, got) => {
                Diagnostic {
                    level: Level::Error,
                    message: format!("Unpacked {} values but expected {}", got, expected),
                    code: Some(INCORRECT_UNPACK_ERROR_CODE.to_owned()),
                    spans: vec![
                        SpanLabel {
                            span: s,
                            style: SpanStyle::Primary,
                            label: None,
                        },
                    ],
                }
            }
            EvalException::Recursion(s, f, stack) => {
                Diagnostic {
                    level: Level::Error,
                    message: format!(
                        "Function {} recursed, call stack:{}",
                        f,
                        stack.iter().rev().fold(String::new(), |a, s| {
                            format!("{}\n  {}", a, s)
                        })
                    ),
                    code: Some(RECURSION_ERROR_CODE.to_owned()),
                    spans: vec![
                        SpanLabel {
                            span: s,
                            style: SpanStyle::Primary,
                            label: Some("Recursive call".to_owned()),
                        },
                    ],
                }
            }
        }
    }
}

/// A trait for loading file using the load statement path.
pub trait FileLoader: Clone {
    /// Open the file given by the load statement `path`.
    fn load(&self, path: &str) -> Result<Environment, EvalException>;
}

/// A structure holding all the data about the evaluation context
/// (scope, load statement resolver, ...)
pub struct EvaluationContext<T: FileLoader> {
    env: Environment,
    loader: T,
    call_stack: Vec<String>,
}

impl<T: FileLoader> EvaluationContext<T> {
    fn new(env: Environment, loader: T) -> Self {
        EvaluationContext {
            call_stack: Vec::new(),
            env,
            loader,
        }
    }
}

// A dummy file loader for inside a function call
impl FileLoader for () {
    fn load(&self, _path: &str) -> Result<Environment, EvalException> {
        // If we reach here, this is a bug.
        unreachable!();
    }
}

// A trait to add an eval function to the AST elements
trait Evaluate<T: FileLoader> {
    fn eval(&self, context: &mut EvaluationContext<T>) -> EvalResult;

    fn set(&self, context: &mut EvaluationContext<T>, new_value: Value) -> EvalResult;
}

impl<T: FileLoader> Evaluate<T> for AstString {
    fn eval(&self, _context: &mut EvaluationContext<T>) -> EvalResult {
        Ok(Value::new(self.node.clone()))
    }

    fn set(&self, _context: &mut EvaluationContext<T>, _new_value: Value) -> EvalResult {
        Err(EvalException::IncorrectLeftValue(self.span))
    }
}

impl<T: FileLoader> Evaluate<T> for AstInt {
    fn eval(&self, _context: &mut EvaluationContext<T>) -> EvalResult {
        Ok(Value::new(self.node.clone()))
    }

    fn set(&self, _context: &mut EvaluationContext<T>, _new_value: Value) -> EvalResult {
        Err(EvalException::IncorrectLeftValue(self.span))
    }
}

fn eval_comprehension_clause<'a, T: FileLoader>(
    context: &mut EvaluationContext<T>,
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
                let iterable = v.eval(context)?;
                for i in t!(iterable.into_iter(), c)? {
                    k.set(context, i)?;
                    if tl.is_empty() {
                        result.push(e.eval(context)?);
                    } else {
                        let mut other = eval_comprehension_clause(context, e, tl)?;
                        result.append(&mut other);
                    }
                }
            }
        }
    }
    Ok(result)
}

impl<T: FileLoader> Evaluate<T> for AstExpr {
    #[allow(unconditional_recursion)]
    fn eval(&self, context: &mut EvaluationContext<T>) -> EvalResult {
        match self.node {
            Expr::Tuple(ref v) => {
                let r = eval_vector!(v, context);
                Ok(tuple::Tuple::new(r.as_slice()))
            }
            Expr::Dot(ref e, ref s) => {
                let left = e.eval(context)?;
                if let Some(v) = context.env.get_type_value(&left, &s.node) {
                    if v.get_type() == "function" {
                        // Insert self so the method see the object it is acting on
                        Ok(function::Function::new_self_call(left.clone(), v))
                    } else {
                        Ok(v)
                    }
                } else {
                    t!(left.get_attr(&s.node), self)
                }
            }
            Expr::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
                let npos = eval_vector!(pos, context);
                let mut nnamed = HashMap::new();
                for &(ref k, ref v) in named.iter() {
                    nnamed.insert(k.eval(context)?.to_str(), v.eval(context)?);
                }
                let nargs = if let &Some(ref x) = args {
                    Some(x.eval(context)?)
                } else {
                    None
                };
                let nkwargs = if let &Some(ref x) = kwargs {
                    Some(x.eval(context)?)
                } else {
                    None
                };
                let f = e.eval(context)?;
                let fname = f.to_str();
                let mut new_stack = context.call_stack.clone();
                if context.call_stack.iter().any(|x| *x == fname) {
                    Err(EvalException::Recursion(self.span, fname, new_stack))
                } else {
                    new_stack.push(fname);
                    t!(
                        e.eval(context)?.call(
                            &new_stack,
                            context.env.clone(),
                            npos,
                            nnamed,
                            nargs,
                            nkwargs,
                        ),
                        self
                    )
                }
            }
            Expr::ArrayIndirection(ref e, ref idx) => {
                let idx = idx.eval(context)?;
                t!(e.eval(context)?.at(idx), self)
            }
            Expr::Slice(ref a, ref start, ref stop, ref stride) => {
                let a = a.eval(context)?;
                let start = match start {
                    &Some(ref e) => Some(e.eval(context)?),
                    &None => None,
                };
                let stop = match stop {
                    &Some(ref e) => Some(e.eval(context)?),
                    &None => None,
                };
                let stride = match stride {
                    &Some(ref e) => Some(e.eval(context)?),
                    &None => None,
                };
                t!(a.slice(start, stop, stride), self)
            }
            Expr::Identifier(ref i) => t!(context.env.get(&i.node), i),
            Expr::IntLitteral(ref i) => Ok(Value::new(i.node)),
            Expr::StringLitteral(ref s) => Ok(Value::new(s.node.clone())),
            Expr::Not(ref s) => Ok(Value::new(!s.eval(context)?.to_bool())),
            Expr::Minus(ref s) => t!(s.eval(context)?.minus(), self),
            Expr::Plus(ref s) => t!(s.eval(context)?.plus(), self),
            Expr::Op(BinOp::Or, ref l, ref r) => Ok(Value::new(
                l.eval(context)?.to_bool() ||
                    r.eval(context)?.to_bool(),
            )),
            Expr::Op(BinOp::And, ref l, ref r) => Ok(Value::new(
                l.eval(context)?.to_bool() &&
                    r.eval(context)?.to_bool(),
            )),
            Expr::Op(BinOp::EqualsTo, ref l, ref r) => Ok(Value::new(
                l.eval(context)? == r.eval(context)?,
            )),
            Expr::Op(BinOp::Different, ref l, ref r) => Ok(Value::new(
                l.eval(context)? != r.eval(context)?,
            )),
            Expr::Op(BinOp::LowerThan, ref l, ref r) => Ok(Value::new(
                l.eval(context)? < r.eval(context)?,
            )),
            Expr::Op(BinOp::GreaterThan, ref l, ref r) => Ok(Value::new(
                l.eval(context)? > r.eval(context)?,
            )),
            Expr::Op(BinOp::LowerOrEqual, ref l, ref r) => Ok(Value::new(
                l.eval(context)? <= r.eval(context)?,
            )),
            Expr::Op(BinOp::GreaterOrEqual, ref l, ref r) => Ok(Value::new(
                l.eval(context)? >= r.eval(context)?,
            )),
            Expr::Op(BinOp::In, ref l, ref r) => t!(r.eval(context)?.is_in(l.eval(context)?), self),
            Expr::Op(BinOp::NotIn, ref l, ref r) => Ok(Value::new(
                t!(
                    r.eval(context)?.is_in(l.eval(context)?),
                    self
                )?
                    .to_bool(),
            )),
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
                t!(l.eval(context)?.div(r.eval(context)?), self)
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
            Expr::ListComprehension(ref e, ref clauses) => {
                let mut r = Vec::new();
                for v in eval_comprehension_clause(context, e, clauses.as_slice())? {
                    r.push(v.clone());
                }
                Ok(Value::from(r))
            }
            Expr::DictComprehension((ref k, ref v), ref clauses) => {
                let mut r = LinkedHashMap::new();
                let tuple = Box::new(Spanned {
                    span: k.span.merge(v.span),
                    node: Expr::Tuple(vec![k.clone(), v.clone()]),
                });
                for e in eval_comprehension_clause(context, &tuple, clauses.as_slice())? {
                    let k = t!(e.at(Value::from(0)), tuple)?;
                    let v = t!(e.at(Value::from(1)), tuple)?;
                    r.insert(k, v);
                }
                Ok(Value::from(r))
            }
        }
    }


    fn set(&self, context: &mut EvaluationContext<T>, new_value: Value) -> EvalResult {
        let ok = Ok(Value::new(None));
        match self.node {
            Expr::Tuple(ref v) |
            Expr::List(ref v) => {
                let l = v.len() as i64;
                let nvl = t!(new_value.length(), self)?;
                if nvl != l {
                    Err(EvalException::IncorrectNumberOfValueToUnpack(
                        self.span,
                        l,
                        nvl,
                    ))
                } else {
                    let mut r = Vec::new();
                    let mut it1 = v.iter();
                    // TODO: the span here should probably include the rvalue
                    let mut it2 = t!(new_value.into_iter(), self)?;
                    for _ in 0..l {
                        r.push(it1.next().unwrap().set(context, it2.next().unwrap())?)
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
                let idx = idx.eval(context)?;
                t!(e.eval(context)?.set_at(idx, new_value), self)?;
                ok
            }
            _ => Err(EvalException::IncorrectLeftValue(self.span)),
        }
    }
}

impl<T: FileLoader> Evaluate<T> for AstStatement {
    fn eval(&self, context: &mut EvaluationContext<T>) -> EvalResult {
        match self.node {
            Statement::Break => Err(EvalException::Break(self.span)),
            Statement::Continue => Err(EvalException::Continue(self.span)),
            Statement::Pass => Ok(Value::new(None)),
            Statement::Return(Some(ref e)) => Err(
                EvalException::Return(self.span, e.eval(context)?),
            ),
            Statement::Return(None) => Err(EvalException::Return(self.span, Value::new(None))),
            Statement::Expression(ref e) => e.eval(context),
            Statement::Assign(ref lhs, AssignOp::Assign, ref rhs) => {
                let rhs = rhs.eval(context)?;
                lhs.set(context, rhs)
            }
            Statement::Assign(ref lhs, AssignOp::Increment, ref rhs) => {
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.add(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Decrement, ref rhs) => {
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.sub(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Multiplier, ref rhs) => {
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.mul(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Divider, ref rhs) => {
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.div(r), self)?)
            }
            Statement::Assign(ref lhs, AssignOp::Percent, ref rhs) => {
                let l = lhs.eval(context)?;
                let r = rhs.eval(context)?;
                lhs.set(context, t!(l.percent(r), self)?)
            }
            Statement::If(ref cond, ref st) => {
                if cond.eval(context)?.to_bool() {
                    st.eval(context)
                } else {
                    Ok(Value::new(None))
                }
            }
            Statement::IfElse(ref cond, ref st1, ref st2) => {
                if cond.eval(context)?.to_bool() {
                    st1.eval(context)
                } else {
                    st2.eval(context)
                }
            }
            Statement::For(AstClause {
                               ref span,
                               node: Clause::For(ref e1, ref e2),
                           },
                           ref st) => {
                let iterable = e2.eval(context)?;
                for v in t!(iterable.into_iter(), span * span)? {
                    e1.set(context, v)?;
                    match st.eval(context) {
                        Err(EvalException::Break(..)) => break,
                        Err(EvalException::Continue(..)) => (),
                        Err(x) => return Err(x),
                        _ => (),
                    }
                }
                Ok(Value::new(None))
            }
            Statement::For(AstClause {
                               span: ref _s,
                               ref node,
                           },
                           ..) => panic!("The parser returned an invalid for clause: {:?}", node),
            Statement::Def(ref name, ref params, ref stmts) => {
                let mut p = Vec::new();
                for ref x in params.iter() {
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
                Ok(Value::new(None))
            }
            Statement::Statements(ref v) => {
                let r = eval_vector!(v, context);
                match r.len() {
                    0 => Ok(Value::new(None)),
                    _ => Ok(r.last().unwrap().clone()),
                }
            }
        }
    }

    fn set(&self, _context: &mut EvaluationContext<T>, _new_value: Value) -> EvalResult {
        Err(EvalException::IncorrectLeftValue(self.span))
    }
}

/// A method for consumption by def funcitons
#[doc(hidden)]
pub fn eval_def(
    call_stack: &Vec<String>,
    signature: &Vec<FunctionParameter>,
    stmts: &AstStatement,
    env: Environment,
    args: Vec<Value>,
) -> ValueResult {
    // argument binding
    let mut it2 = args.iter();
    for s in signature.iter() {
        match s {
            &FunctionParameter::Normal(ref v) |
            &FunctionParameter::WithDefaultValue(ref v, ..) |
            &FunctionParameter::ArgsArray(ref v) |
            &FunctionParameter::KWArgsDict(ref v) => {
                match env.set(v, it2.next().unwrap().clone()) {
                    Err(x) => return Err(x.into()),
                    _ => (),
                }
            }
        }
    }
    let mut ctx = EvaluationContext {
        call_stack: call_stack.clone(),
        env,
        loader: (),
    };
    match stmts.eval(&mut ctx) {
        Err(EvalException::Return(_s, ret)) => Ok(ret),
        Err(x) => Err(ValueError::DiagnosedError(x.into())),
        Ok(..) => Ok(Value::new(None)),
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
/// * build: set to true if you want to evaluate a BUILD file or false to evaluate a .bzl file
/// * lexer: the custom lexer to use
/// * env: the environment to mutate during the evaluation
/// * file_loader: the [FileLoader](trait.FileLoader.html) to react to `load()` statements.
fn eval_lexer<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>, T3: FileLoader>(
    map: &Arc<Mutex<CodeMap>>,
    filename: &str,
    content: &str,
    build: bool,
    lexer: T2,
    env: &mut Environment,
    file_loader: T3,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), file_loader);
    match parse_lexer(map, filename, content, build, lexer)?.eval(
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
/// * build: set to true if you want to evaluate a BUILD file or false to evaluate a .bzl file
/// * env: the environment to mutate during the evaluation
/// * file_loader: the [FileLoader](trait.FileLoader.html) to react to `load()` statements.
pub fn eval<T: FileLoader>(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    content: &str,
    build: bool,
    env: &mut Environment,
    file_loader: T,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), file_loader);
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
/// * build: set to true if you want to evaluate a BUILD file or false to evaluate a .bzl file
/// * env: the environment to mutate during the evaluation
/// * file_loader: the [FileLoader](trait.FileLoader.html) to react to `load()` statements.
pub fn eval_file<T: FileLoader>(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    build: bool,
    env: &mut Environment,
    file_loader: T,
) -> Result<Value, Diagnostic> {
    let mut context = EvaluationContext::new(env.clone(), file_loader);
    match parse_file(map, path, build)?.eval(&mut context) {
        Ok(v) => Ok(v),
        Err(p) => Err(p.into()),
    }
}

pub mod simple;
pub mod interactive;
pub mod repl;

#[cfg(test)]
#[macro_use]
pub mod testutil;

#[cfg(test)]
mod tests;
