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

//! AST for parsed starlark files.

use super::lexer;
use crate::eval::compr::ComprehensionCompiled;
use crate::eval::def::DefCompiled;
use crate::syntax::dialect::Dialect;
use codemap::{Span, Spanned};
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use lalrpop_util;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::{Display, Formatter};

// Boxed types used for storing information from the parsing will be used especially for the
// location of the AST item
#[doc(hidden)]
pub type AstExpr = Box<Spanned<Expr>>;
#[doc(hidden)]
pub type AstArgument = Spanned<Argument>;
#[doc(hidden)]
pub type AstString = Spanned<String>;
#[doc(hidden)]
pub type AstParameter = Spanned<Parameter>;
#[doc(hidden)]
pub type AstClause = Spanned<Clause>;
#[doc(hidden)]
pub type AstInt = Spanned<i64>;
#[doc(hidden)]
pub type AstStatement = Box<Spanned<Statement>>;

// Critical Semantic
const POSITIONAL_ARGUMENT_AFTER_NON_POSITIONAL_ERROR_CODE: &str = "CS00";
const NAMED_ARGUMENT_AFTER_KWARGS_DICT_ERROR_CODE: &str = "CS01";
const ARGS_ARRAY_AFTER_ANOTHER_ARGS_OR_KWARGS_ERROR_CODE: &str = "CS02";
const MULTIPLE_KWARGS_DICT_IN_ARGS_ERROR_CODE: &str = "CS03";
const POSITIONAL_PARAMETER_AFTER_NON_POSITIONAL_ERROR_CODE: &str = "CS04";
const DEFAULT_PARAM_AFTER_ARGS_OR_KWARGS_ERROR_CODE: &str = "CS05";
const ARGS_AFTER_ARGS_OR_KWARGS_ERROR_CODE: &str = "CS06";
const MULTIPLE_KWARGS_DICTS_IN_PARAMS_ERROR_CODE: &str = "CS07";
const DUPLICATED_PARAM_NAME_ERROR_CODE: &str = "CS08";
const BREAK_OR_CONTINUE_OUTSIDE_OF_LOOP_ERROR_CODE: &str = "CS09";

#[doc(hidden)]
pub trait ToAst<T> {
    fn to_ast(self, span: Span) -> T;
}

macro_rules! to_ast_trait {
    ($t1:ty, $t2:ty, $t3:ident) => {
        impl ToAst<$t2> for $t1 {
            fn to_ast(self, span: Span) -> $t2 {
                $t3::new(Spanned { span, node: self })
            }
        }
    };
    ($t1:ty, $t2:ty) => {
        impl ToAst<$t2> for $t1 {
            fn to_ast(self, span: Span) -> $t2 {
                Spanned { span, node: self }
            }
        }
    };
}

to_ast_trait!(i64, AstInt);
to_ast_trait!(String, AstString);

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum Argument {
    Positional(AstExpr),
    Named(AstString, AstExpr),
    ArgsArray(AstExpr),
    KWArgsDict(AstExpr),
}
to_ast_trait!(Argument, AstArgument);

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum Parameter {
    Normal(AstString),
    WithDefaultValue(AstString, AstExpr),
    Args(AstString),
    KWArgs(AstString),
}
to_ast_trait!(Parameter, AstParameter);

impl Parameter {
    pub fn name(&self) -> &str {
        match self {
            Parameter::Normal(n) => &n.node,
            Parameter::WithDefaultValue(n, ..) => &n.node,
            Parameter::Args(n) => &n.node,
            Parameter::KWArgs(n) => &n.node,
        }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum Expr {
    Tuple(Vec<AstExpr>),
    Dot(AstExpr, AstString),
    Call(
        AstExpr,
        Vec<AstExpr>,
        Vec<(AstString, AstExpr)>,
        Option<AstExpr>,
        Option<AstExpr>,
    ),
    ArrayIndirection(AstExpr, AstExpr),
    Slice(AstExpr, Option<AstExpr>, Option<AstExpr>, Option<AstExpr>),
    Identifier(AstString),
    // local variable index
    Slot(usize, AstString),
    IntLiteral(AstInt),
    StringLiteral(AstString),
    Not(AstExpr),
    Minus(AstExpr),
    Plus(AstExpr),
    Op(BinOp, AstExpr, AstExpr),
    If(AstExpr, AstExpr, AstExpr), // Order: condition, v1, v2 <=> v1 if condition else v2
    List(Vec<AstExpr>),
    Set(Vec<AstExpr>),
    Dict(Vec<(AstExpr, AstExpr)>),
    ListComprehension(AstExpr, Vec<AstClause>),
    SetComprehension(AstExpr, Vec<AstClause>),
    DictComprehension((AstExpr, AstExpr), Vec<AstClause>),
    ComprehensionCompiled(ComprehensionCompiled),
}
to_ast_trait!(Expr, AstExpr, Box);

impl Expr {
    pub fn check_call(
        f: AstExpr,
        args: Vec<AstArgument>,
    ) -> Result<Expr, lalrpop_util::ParseError<u64, lexer::Token, lexer::LexerError>> {
        let mut pos_args = Vec::new();
        let mut named_args = Vec::new();
        let mut args_array = None;
        let mut kwargs_dict = None;
        let mut stage = 0;
        for arg in args {
            match arg.node {
                Argument::Positional(s) => {
                    if stage > 0 {
                        return Err(lalrpop_util::ParseError::User {
                            error: lexer::LexerError::WrappedError {
                                span: arg.span,
                                code: POSITIONAL_ARGUMENT_AFTER_NON_POSITIONAL_ERROR_CODE,
                                label: "positional argument after non positional",
                            },
                        });
                    } else {
                        pos_args.push(s);
                    }
                }
                Argument::Named(n, v) => {
                    if stage > 2 {
                        return Err(lalrpop_util::ParseError::User {
                            error: lexer::LexerError::WrappedError {
                                span: arg.span,
                                code: NAMED_ARGUMENT_AFTER_KWARGS_DICT_ERROR_CODE,
                                label: "named argument after kwargs dictionary",
                            },
                        });
                    } else {
                        if stage == 0 {
                            stage = 1;
                        }
                        named_args.push((n, v));
                    }
                }
                Argument::ArgsArray(v) => {
                    if stage > 1 {
                        return Err(lalrpop_util::ParseError::User {
                            error: lexer::LexerError::WrappedError {
                                span: arg.span,
                                code: ARGS_ARRAY_AFTER_ANOTHER_ARGS_OR_KWARGS_ERROR_CODE,
                                label: "Args array after another args or kwargs",
                            },
                        });
                    } else {
                        stage = 2;
                        args_array = Some(v);
                    }
                }
                Argument::KWArgsDict(d) => {
                    if stage == 3 {
                        return Err(lalrpop_util::ParseError::User {
                            error: lexer::LexerError::WrappedError {
                                span: arg.span,
                                code: MULTIPLE_KWARGS_DICT_IN_ARGS_ERROR_CODE,
                                label: "Multiple kwargs dictionary in arguments",
                            },
                        });
                    } else {
                        stage = 3;
                        kwargs_dict = Some(d);
                    }
                }
            }
        }
        Ok(Expr::Call(f, pos_args, named_args, args_array, kwargs_dict))
    }

    pub(crate) fn collect_locals_from_assign_expr(
        expr: &AstExpr,
        local_names_to_indices: &mut HashMap<String, usize>,
    ) {
        match expr.node {
            Expr::Tuple(ref exprs) | Expr::List(ref exprs) => {
                for expr in exprs {
                    Expr::collect_locals_from_assign_expr(expr, local_names_to_indices);
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

    pub(crate) fn transform_locals_to_slots(
        expr: AstExpr,
        locals: &HashMap<String, usize>,
    ) -> AstExpr {
        Box::new(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Tuple(exprs) => Expr::Tuple(
                    exprs
                        .into_iter()
                        .map(|expr| Expr::transform_locals_to_slots(expr, locals))
                        .collect(),
                ),
                Expr::List(exprs) => Expr::List(
                    exprs
                        .into_iter()
                        .map(|expr| Expr::transform_locals_to_slots(expr, locals))
                        .collect(),
                ),
                Expr::Set(exprs) => Expr::Set(
                    exprs
                        .into_iter()
                        .map(|expr| Expr::transform_locals_to_slots(expr, locals))
                        .collect(),
                ),
                Expr::Dict(pairs) => Expr::Dict(
                    pairs
                        .into_iter()
                        .map(|(key, value)| {
                            (
                                Expr::transform_locals_to_slots(key, locals),
                                Expr::transform_locals_to_slots(value, locals),
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
                    Expr::Dot(Expr::transform_locals_to_slots(left, locals), right)
                }
                Expr::Call(function, args, kwargs, star_args, star_star_kwargs) => Expr::Call(
                    Expr::transform_locals_to_slots(function, locals),
                    args.into_iter()
                        .map(|expr| Expr::transform_locals_to_slots(expr, locals))
                        .collect(),
                    kwargs
                        .into_iter()
                        .map(|(name, value)| (name, Expr::transform_locals_to_slots(value, locals)))
                        .collect(),
                    star_args.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                    star_star_kwargs.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                ),
                Expr::ArrayIndirection(array, index) => Expr::ArrayIndirection(
                    Expr::transform_locals_to_slots(array, locals),
                    Expr::transform_locals_to_slots(index, locals),
                ),
                Expr::Slice(array, p1, p2, p3) => Expr::Slice(
                    array,
                    p1.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                    p2.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                    p3.map(|expr| Expr::transform_locals_to_slots(expr, locals)),
                ),
                Expr::Not(expr) => Expr::Not(Expr::transform_locals_to_slots(expr, locals)),
                Expr::Minus(expr) => Expr::Minus(Expr::transform_locals_to_slots(expr, locals)),
                Expr::Plus(expr) => Expr::Plus(Expr::transform_locals_to_slots(expr, locals)),
                Expr::Op(op, left, right) => Expr::Op(
                    op,
                    Expr::transform_locals_to_slots(left, locals),
                    Expr::transform_locals_to_slots(right, locals),
                ),
                Expr::If(cond, then_expr, else_expr) => Expr::If(
                    Expr::transform_locals_to_slots(cond, locals),
                    Expr::transform_locals_to_slots(then_expr, locals),
                    Expr::transform_locals_to_slots(else_expr, locals),
                ),
                n @ Expr::IntLiteral(..) | n @ Expr::StringLiteral(..) => n,
                n @ Expr::DictComprehension(..)
                | n @ Expr::ListComprehension(..)
                | n @ Expr::SetComprehension(..)
                | n @ Expr::ComprehensionCompiled(..) => {
                    // TODO: access parent scope variables by index, not by name.
                    n
                }
            },
        })
    }

    pub(crate) fn compile(expr: AstExpr) -> Result<AstExpr, Diagnostic> {
        Ok(Box::new(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Tuple(exprs) => Expr::Tuple(
                    exprs
                        .into_iter()
                        .map(Expr::compile)
                        .collect::<Result<_, _>>()?,
                ),
                Expr::List(exprs) => Expr::List(
                    exprs
                        .into_iter()
                        .map(Expr::compile)
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Set(exprs) => Expr::Set(
                    exprs
                        .into_iter()
                        .map(Expr::compile)
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Dict(exprs) => Expr::Dict(
                    exprs
                        .into_iter()
                        .map(|(k, v)| Ok((Expr::compile(k)?, Expr::compile(v)?)))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::If(cond, then_expr, else_expr) => Expr::If(
                    Expr::compile(cond)?,
                    Expr::compile(then_expr)?,
                    Expr::compile(else_expr)?,
                ),
                Expr::Dot(left, right) => Expr::Dot(Expr::compile(left)?, right),
                Expr::Call(left, positional, named, args, kwargs) => Expr::Call(
                    Expr::compile(left)?,
                    positional
                        .into_iter()
                        .map(Expr::compile)
                        .collect::<Result<_, _>>()?,
                    named
                        .into_iter()
                        .map(|(name, value)| Ok((name, Expr::compile(value)?)))
                        .collect::<Result<_, _>>()?,
                    args.map(Expr::compile).transpose()?,
                    kwargs.map(Expr::compile).transpose()?,
                ),
                Expr::ArrayIndirection(array, index) => {
                    Expr::ArrayIndirection(Expr::compile(array)?, Expr::compile(index)?)
                }
                Expr::Slice(collection, a, b, c) => Expr::Slice(
                    Expr::compile(collection)?,
                    a.map(Expr::compile).transpose()?,
                    b.map(Expr::compile).transpose()?,
                    c.map(Expr::compile).transpose()?,
                ),
                Expr::Not(expr) => Expr::Not(Expr::compile(expr)?),
                Expr::Minus(expr) => Expr::Minus(Expr::compile(expr)?),
                Expr::Plus(expr) => Expr::Plus(Expr::compile(expr)?),
                Expr::Op(op, left, right) => {
                    Expr::Op(op, Expr::compile(left)?, Expr::compile(right)?)
                }
                Expr::ListComprehension(expr, clauses) => {
                    Expr::ComprehensionCompiled(ComprehensionCompiled::new_list(expr, clauses)?)
                }
                Expr::SetComprehension(expr, clauses) => {
                    Expr::ComprehensionCompiled(ComprehensionCompiled::new_set(expr, clauses)?)
                }
                Expr::DictComprehension((key, value), clauses) => Expr::ComprehensionCompiled(
                    ComprehensionCompiled::new_dict(key, value, clauses)?,
                ),
                Expr::ComprehensionCompiled(..) => unreachable!(),
                e @ Expr::Slot(..)
                | e @ Expr::Identifier(..)
                | e @ Expr::StringLiteral(..)
                | e @ Expr::IntLiteral(..) => e,
            },
        }))
    }
}

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum Clause {
    For(AstExpr, AstExpr),
    If(AstExpr),
}
to_ast_trait!(Clause, AstClause);

#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Or,
    And,
    EqualsTo,
    Different,
    LowerThan,
    GreaterThan,
    LowerOrEqual,
    GreaterOrEqual,
    In,
    NotIn,
    Substraction,
    Addition,
    Multiplication,
    Percent,
    Division,
    FloorDivision,
    Pipe,
}

#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub enum AssignOp {
    Assign,
    Increment,
    Decrement,
    Multiplier,
    Divider,
    FloorDivider,
    Percent,
}

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum Statement {
    Break,
    Continue,
    Pass,
    Return(Option<AstExpr>),
    Expression(AstExpr),
    Assign(AstExpr, AssignOp, AstExpr),
    Statements(Vec<AstStatement>),
    If(AstExpr, AstStatement),
    IfElse(AstExpr, AstStatement, AstStatement),
    For(AstExpr, AstExpr, AstStatement),
    Def(AstString, Vec<AstParameter>, AstStatement),
    /// Post-processed `def` statement
    DefCompiled(DefCompiled),
    Load(AstString, Vec<(AstString, AstString)>),
}
to_ast_trait!(Statement, AstStatement, Box);

macro_rules! test_param_name {
    ($argset:ident, $n:ident, $arg:ident) => {{
        if $argset.contains(&$n.node) {
            return Err(lalrpop_util::ParseError::User {
                error: lexer::LexerError::WrappedError {
                    span: $arg.span,
                    code: DUPLICATED_PARAM_NAME_ERROR_CODE,
                    label: "duplicated parameter name",
                },
            });
        }
        $argset.insert($n.node.clone());
    }};
}

impl Statement {
    pub fn check_def(
        name: AstString,
        parameters: Vec<AstParameter>,
        stmts: AstStatement,
    ) -> Result<Statement, lalrpop_util::ParseError<u64, lexer::Token, lexer::LexerError>> {
        {
            let mut stage = 0;
            let mut argset = HashSet::new();
            for arg in parameters.iter() {
                match arg.node {
                    Parameter::Normal(ref n) => {
                        if stage > 0 {
                            return Err(lalrpop_util::ParseError::User {
                                error: lexer::LexerError::WrappedError {
                                    span: arg.span,
                                    code: POSITIONAL_PARAMETER_AFTER_NON_POSITIONAL_ERROR_CODE,
                                    label: "positional parameter after non positional",
                                },
                            });
                        }
                        test_param_name!(argset, n, arg);
                    }
                    Parameter::WithDefaultValue(ref n, ..) => {
                        if stage > 1 {
                            return Err(lalrpop_util::ParseError::User {
                                error: lexer::LexerError::WrappedError {
                                    span: arg.span,
                                    code: DEFAULT_PARAM_AFTER_ARGS_OR_KWARGS_ERROR_CODE,
                                    label:
                                        "Default parameter after args array or kwargs dictionary",
                                },
                            });
                        } else if stage == 0 {
                            stage = 1;
                        }
                        test_param_name!(argset, n, arg);
                    }
                    Parameter::Args(ref n) => {
                        if stage > 1 {
                            return Err(lalrpop_util::ParseError::User {
                                error: lexer::LexerError::WrappedError {
                                    span: arg.span,
                                    code: ARGS_AFTER_ARGS_OR_KWARGS_ERROR_CODE,
                                    label: "Args parameter after another args or kwargs parameter",
                                },
                            });
                        } else {
                            stage = 2;
                        }
                        test_param_name!(argset, n, arg);
                    }
                    Parameter::KWArgs(ref n) => {
                        if stage == 3 {
                            return Err(lalrpop_util::ParseError::User {
                                error: lexer::LexerError::WrappedError {
                                    span: arg.span,
                                    code: MULTIPLE_KWARGS_DICTS_IN_PARAMS_ERROR_CODE,
                                    label: "Multiple kwargs dictionary in parameters",
                                },
                            });
                        } else {
                            stage = 3;
                        }
                        test_param_name!(argset, n, arg);
                    }
                }
            }
        }
        Ok(Statement::Def(name, parameters, stmts))
    }

    /// Validate `break` and `continue` is only used inside loops
    fn validate_break_continue(stmt: &AstStatement) -> Result<(), Diagnostic> {
        match stmt.node {
            Statement::Break | Statement::Continue => {
                let kw = if let Statement::Break = stmt.node {
                    "break"
                } else {
                    "continue"
                };
                Err(Diagnostic {
                    level: Level::Error,
                    message: format!("{} cannot be used outside of loop", kw),
                    code: Some(BREAK_OR_CONTINUE_OUTSIDE_OF_LOOP_ERROR_CODE.to_owned()),
                    spans: vec![SpanLabel {
                        span: stmt.span,
                        label: None,
                        style: SpanStyle::Primary,
                    }],
                })
            }
            Statement::Def(.., ref stmt) => Statement::validate_break_continue(stmt),
            Statement::DefCompiled(..) => unreachable!(),
            Statement::If(.., ref then_block) => Statement::validate_break_continue(then_block),
            Statement::IfElse(.., ref then_block, ref else_block) => {
                Statement::validate_break_continue(then_block)?;
                Statement::validate_break_continue(else_block)?;
                Ok(())
            }
            Statement::Statements(ref stmts) => {
                for stmt in stmts {
                    Statement::validate_break_continue(stmt)?;
                }
                Ok(())
            }
            Statement::For(..) => {
                // No need to check loop body, because `break` and `continue`
                // are valid anywhere in loop body.
                Ok(())
            }
            Statement::Return(..)
            | Statement::Expression(..)
            | Statement::Pass
            | Statement::Assign(..)
            | Statement::Load(..) => {
                // These statements do not contain nested statements
                Ok(())
            }
        }
    }

    pub(crate) fn compile(stmt: AstStatement) -> Result<AstStatement, Diagnostic> {
        Ok(Box::new(Spanned {
            span: stmt.span,
            node: match stmt.node {
                Statement::DefCompiled(..) => unreachable!(),
                Statement::Def(name, params, suite) => {
                    Statement::DefCompiled(DefCompiled::new(name, params, suite)?)
                }
                Statement::For(var, over, body) => Statement::For(
                    Expr::compile(var)?,
                    Expr::compile(over)?,
                    Statement::compile(body)?,
                ),
                Statement::Return(expr) => Statement::Return(expr.map(Expr::compile).transpose()?),
                Statement::If(cond, then_block) => {
                    Statement::If(cond, Statement::compile(then_block)?)
                }
                Statement::IfElse(conf, then_block, else_block) => Statement::IfElse(
                    conf,
                    Statement::compile(then_block)?,
                    Statement::compile(else_block)?,
                ),
                Statement::Statements(stmts) => Statement::Statements(
                    stmts
                        .into_iter()
                        .map(Statement::compile)
                        .collect::<Result<_, _>>()?,
                ),
                Statement::Expression(e) => Statement::Expression(Expr::compile(e)?),
                Statement::Assign(left, op, right) => {
                    Statement::Assign(Expr::compile(left)?, op, Expr::compile(right)?)
                }
                s @ Statement::Load(..)
                | s @ Statement::Pass
                | s @ Statement::Break
                | s @ Statement::Continue => s,
            },
        }))
    }

    pub(crate) fn compile_mod(
        stmt: AstStatement,
        _dialect: Dialect,
    ) -> Result<AstStatement, Diagnostic> {
        Statement::validate_break_continue(&stmt)?;
        let stmt = Statement::compile(stmt)?;
        Ok(stmt)
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            BinOp::Or => f.write_str(" or "),
            BinOp::And => f.write_str(" and "),
            BinOp::EqualsTo => f.write_str(" == "),
            BinOp::Different => f.write_str(" != "),
            BinOp::LowerThan => f.write_str(" < "),
            BinOp::GreaterThan => f.write_str(" > "),
            BinOp::LowerOrEqual => f.write_str(" <= "),
            BinOp::GreaterOrEqual => f.write_str(" >= "),
            BinOp::In => f.write_str(" in "),
            BinOp::NotIn => f.write_str(" not in "),
            BinOp::Substraction => f.write_str(" - "),
            BinOp::Addition => f.write_str(" + "),
            BinOp::Multiplication => f.write_str(" * "),
            BinOp::Percent => f.write_str(" % "),
            BinOp::Division => f.write_str(" / "),
            BinOp::FloorDivision => f.write_str(" // "),
            BinOp::Pipe => f.write_str(" | "),
        }
    }
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            AssignOp::Assign => f.write_str(" = "),
            AssignOp::Increment => f.write_str(" += "),
            AssignOp::Decrement => f.write_str(" += "),
            AssignOp::Multiplier => f.write_str(" *= "),
            AssignOp::Divider => f.write_str(" /= "),
            AssignOp::FloorDivider => f.write_str(" //= "),
            AssignOp::Percent => f.write_str(" %= "),
        }
    }
}

fn comma_separated_fmt<I, F>(
    f: &mut Formatter<'_>,
    v: &[I],
    converter: F,
    for_tuple: bool,
) -> fmt::Result
where
    F: Fn(&I, &mut Formatter<'_>) -> fmt::Result,
{
    for (i, e) in v.iter().enumerate() {
        f.write_str(if i == 0 { "" } else { ", " })?;
        converter(e, f)?;
    }
    if v.len() == 1 && for_tuple {
        f.write_str(",")?;
    }
    Ok(())
}

fn fmt_string_literal(f: &mut Formatter<'_>, s: &str) -> fmt::Result {
    f.write_str("\"")?;
    for c in s.chars() {
        match c {
            '\n' => f.write_str("\\n")?,
            '\t' => f.write_str("\\t")?,
            '\r' => f.write_str("\\r")?,
            '\0' => f.write_str("\\0")?,
            '"' => f.write_str("\\\"")?,
            '\\' => f.write_str("\\\\")?,
            x => f.write_str(&x.to_string())?,
        }
    }
    f.write_str("\"")
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Expr::Tuple(ref e) => {
                f.write_str("(")?;
                comma_separated_fmt(f, e, |x, f| x.node.fmt(f), true)?;
                f.write_str(")")
            }
            Expr::Dot(ref e, ref s) => write!(f, "{}.{}", e.node, s.node),
            Expr::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
                write!(f, "{}(", e.node)?;
                let mut first = true;
                for a in pos {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    a.node.fmt(f)?;
                }
                for &(ref k, ref v) in named {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    write!(f, "{} = {}", k.node, v.node)?;
                }
                if let Some(ref x) = args {
                    if !first {
                        f.write_str(", ")?;
                    }
                    first = false;
                    write!(f, "*{}", x.node)?;
                }
                if let Some(ref x) = kwargs {
                    if !first {
                        f.write_str(", ")?;
                    }
                    write!(f, "**{}", x.node)?;
                }
                f.write_str(")")
            }
            Expr::ArrayIndirection(ref e, ref i) => write!(f, "{}[{}]", e.node, i.node),
            Expr::Slice(ref e, ref i1, ref i2, ref i3) => {
                write!(f, "{}[]", e.node)?;
                if let Some(ref x) = i1 {
                    write!(f, "{}:", x.node)?
                } else {
                    f.write_str(":")?
                }
                if let Some(ref x) = i2 {
                    x.node.fmt(f)?
                }
                if let Some(ref x) = i3 {
                    write!(f, ":{}", x.node)?
                }
                Ok(())
            }
            Expr::Identifier(ref s) | Expr::Slot(_, ref s) => s.node.fmt(f),
            Expr::IntLiteral(ref i) => i.node.fmt(f),
            Expr::Not(ref e) => write!(f, "(not {})", e.node),
            Expr::Minus(ref e) => write!(f, "-{}", e.node),
            Expr::Plus(ref e) => write!(f, "+{}", e.node),
            Expr::Op(ref op, ref l, ref r) => write!(f, "({}{}{})", l.node, op, r.node),
            Expr::If(ref cond, ref v1, ref v2) => {
                write!(f, "({} if {} else {})", v1.node, cond.node, v2.node)
            }
            Expr::List(ref v) => {
                f.write_str("[")?;
                comma_separated_fmt(f, v, |x, f| x.node.fmt(f), false)?;
                f.write_str("]")
            }
            Expr::Set(ref v) => {
                f.write_str("{")?;
                comma_separated_fmt(f, v, |x, f| x.node.fmt(f), false)?;
                f.write_str("}")
            }
            Expr::Dict(ref v) => {
                f.write_str("{")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}: {}", x.0.node, x.1.node), false)?;
                f.write_str("}")
            }
            Expr::ListComprehension(ref e, ref v) => {
                write!(f, "[{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| x.node.fmt(f), false)?;
                f.write_str("]")
            }
            Expr::SetComprehension(ref e, ref v) => {
                write!(f, "{{{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| x.node.fmt(f), false)?;
                f.write_str("}}")
            }
            Expr::DictComprehension((ref k, ref v), ref c) => {
                write!(f, "{{{}: {}", k.node, v.node)?;
                comma_separated_fmt(f, c, |x, f| x.node.fmt(f), false)?;
                f.write_str("}}")
            }
            Expr::ComprehensionCompiled(ref c) => fmt::Display::fmt(&c.to_raw(), f),
            Expr::StringLiteral(ref s) => fmt_string_literal(f, &s.node),
        }
    }
}

impl Display for Argument {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Argument::Positional(ref s) => s.node.fmt(f),
            Argument::Named(ref s, ref e) => write!(f, "{} = {}", s.node, e.node),
            Argument::ArgsArray(ref s) => write!(f, "*{}", s.node),
            Argument::KWArgsDict(ref s) => write!(f, "**{}", s.node),
        }
    }
}

impl Display for Parameter {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Parameter::Normal(ref s) => s.node.fmt(f),
            Parameter::WithDefaultValue(ref s, ref e) => write!(f, "{} = {}", s.node, e.node),
            Parameter::Args(ref s) => write!(f, "*{}", s.node),
            Parameter::KWArgs(ref s) => write!(f, "**{}", s.node),
        }
    }
}

impl Display for Clause {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Clause::For(ref t, ref e) => write!(f, " for {} in {}", t.node, e.node),
            Clause::If(ref t) => write!(f, " if {}", t.node),
        }
    }
}

impl Statement {
    fn fmt_with_tab(&self, f: &mut Formatter<'_>, tab: String) -> fmt::Result {
        match *self {
            Statement::Break => writeln!(f, "{}break", tab),
            Statement::Continue => writeln!(f, "{}continue", tab),
            Statement::Pass => writeln!(f, "{}pass", tab),
            Statement::Return(Some(ref e)) => writeln!(f, "{}return {}", tab, e.node),
            Statement::Return(None) => writeln!(f, "{}return", tab),
            Statement::Expression(ref e) => writeln!(f, "{}{}", tab, e.node),
            Statement::Assign(ref l, ref op, ref r) => {
                writeln!(f, "{}{}{}{}", tab, l.node, op, r.node)
            }
            Statement::Statements(ref v) => {
                for s in v {
                    s.node.fmt_with_tab(f, tab.clone())?;
                }
                Ok(())
            }
            Statement::If(ref cond, ref suite) => {
                writeln!(f, "{}if {}:", tab, cond.node)?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::IfElse(ref cond, ref suite1, ref suite2) => {
                writeln!(f, "{}if {}:", tab, cond.node)?;
                suite1.node.fmt_with_tab(f, tab.clone() + "  ")?;
                writeln!(f, "{}else:", tab)?;
                suite2.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::For(ref bind, ref coll, ref suite) => {
                writeln!(f, "{}for {} in {}:", tab, bind.node, coll.node)?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::Def(ref name, ref params, ref suite)
            | Statement::DefCompiled(DefCompiled {
                ref name,
                ref params,
                ref suite,
                ..
            }) => {
                write!(f, "{}def {}(", tab, name.node)?;
                comma_separated_fmt(f, params, |x, f| x.node.fmt(f), false)?;
                f.write_str("):\n")?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::Load(ref filename, ref v) => {
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
        }
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.fmt_with_tab(f, "".to_owned())
    }
}
