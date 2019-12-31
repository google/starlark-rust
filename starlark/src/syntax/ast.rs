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
use crate::eval::locals::LocalsBuilder;
use crate::syntax::fmt::comma_separated_fmt;
use crate::syntax::fmt::fmt_string_literal;
use crate::syntax::fmt::indent;
use crate::values::string::rc::RcString;
use codemap::{Span, Spanned};
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use lalrpop_util;
use std::collections::HashSet;
use std::fmt;
use std::fmt::{Display, Formatter};

// Boxed types used for storing information from the parsing will be used especially for the
// location of the AST item
#[doc(hidden)]
pub(crate) type AstExpr = Box<Spanned<Expr>>;
#[doc(hidden)]
pub type AstAugmentedAssignTargetExpr = Spanned<AugmentedAssignTargetExpr>;
#[doc(hidden)]
pub type AstAssignTargetExpr = Spanned<AssignTargetExpr>;
#[doc(hidden)]
pub type AstArgument = Spanned<Argument>;
#[doc(hidden)]
pub type AstString = Spanned<RcString>;
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
const INCORRECT_AUGMENTED_ASSIGNMENT_TARGET_ERROR_CODE: &str = "CS10";
const INCORRECT_ASSIGNMENT_TARGET_ERROR_CODE: &str = "CS11";
const AUGMENTED_ASSIGN_IN_MOD: &str = "CS12";

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

impl ToAst<AstString> for String {
    fn to_ast(self, span: Span) -> Spanned<RcString> {
        Spanned {
            span,
            node: RcString::from(self),
        }
    }
}

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
    pub(crate) fn name(&self) -> RcString {
        match self {
            Parameter::Normal(n) => n.node.clone(),
            Parameter::WithDefaultValue(n, ..) => n.node.clone(),
            Parameter::Args(n) => n.node.clone(),
            Parameter::KWArgs(n) => n.node.clone(),
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
    IntLiteral(AstInt),
    StringLiteral(AstString),
    Not(AstExpr),
    And(AstExpr, AstExpr),
    Or(AstExpr, AstExpr),
    BinOp(BinOp, AstExpr, AstExpr),
    UnOp(UnOp, AstExpr),
    If(AstExpr, AstExpr, AstExpr), // Order: condition, v1, v2 <=> v1 if condition else v2
    List(Vec<AstExpr>),
    Set(Vec<AstExpr>),
    Dict(Vec<(AstExpr, AstExpr)>),
    ListComprehension(AstExpr, Vec<AstClause>),
    SetComprehension(AstExpr, Vec<AstClause>),
    DictComprehension((AstExpr, AstExpr), Vec<AstClause>),
}
to_ast_trait!(Expr, AstExpr, Box);

/// `x` in `x = a`
#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum AssignTargetExpr {
    Identifier(AstString),
    Dot(AstExpr, AstString),
    ArrayIndirection(AstExpr, AstExpr),
    Subtargets(Vec<AstAssignTargetExpr>),
}
to_ast_trait!(AssignTargetExpr, AstAssignTargetExpr);

/// `x` in `x += a`
#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum AugmentedAssignTargetExpr {
    Identifier(AstString),
    Dot(AstExpr, AstString),
    ArrayIndirection(AstExpr, AstExpr),
}
to_ast_trait!(AugmentedAssignTargetExpr, AstAugmentedAssignTargetExpr);

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

    pub(crate) fn collect_locals(expr: &AstExpr, locals_builder: &mut LocalsBuilder) {
        match expr.node {
            Expr::Tuple(ref exprs) | Expr::List(ref exprs) | Expr::Set(ref exprs) => {
                for expr in exprs {
                    Expr::collect_locals(expr, locals_builder);
                }
            }
            Expr::Dict(ref pairs) => {
                for pair in pairs {
                    Expr::collect_locals(&pair.0, locals_builder);
                    Expr::collect_locals(&pair.1, locals_builder);
                }
            }
            Expr::Dot(ref object, ref _field) => {
                Expr::collect_locals(object, locals_builder);
            }
            Expr::ArrayIndirection(ref array, ref index) => {
                Expr::collect_locals(array, locals_builder);
                Expr::collect_locals(index, locals_builder);
            }
            Expr::Call(ref func, ref args, ref named, ref star, ref star_star) => {
                Expr::collect_locals(func, locals_builder);
                for arg in args {
                    Expr::collect_locals(arg, locals_builder);
                }
                for arg in named {
                    Expr::collect_locals(&arg.1, locals_builder);
                }
                if let Some(star) = star {
                    Expr::collect_locals(star, locals_builder);
                }
                if let Some(star_star) = star_star {
                    Expr::collect_locals(star_star, locals_builder);
                }
            }
            Expr::Slice(ref array, ref a, ref b, ref c) => {
                Expr::collect_locals(array, locals_builder);
                if let Some(ref a) = a {
                    Expr::collect_locals(a, locals_builder);
                }
                if let Some(ref b) = b {
                    Expr::collect_locals(b, locals_builder);
                }
                if let Some(ref c) = c {
                    Expr::collect_locals(c, locals_builder);
                }
            }
            Expr::Identifier(..) | Expr::IntLiteral(..) | Expr::StringLiteral(..) => {}
            Expr::Not(ref expr) | Expr::UnOp(_, ref expr) => {
                Expr::collect_locals(expr, locals_builder);
            }
            Expr::BinOp(_, ref lhs, ref rhs)
            | Expr::And(ref lhs, ref rhs)
            | Expr::Or(ref lhs, ref rhs) => {
                Expr::collect_locals(lhs, locals_builder);
                Expr::collect_locals(rhs, locals_builder);
            }
            Expr::If(ref cond, ref then_expr, ref else_expr) => {
                Expr::collect_locals(cond, locals_builder);
                Expr::collect_locals(then_expr, locals_builder);
                Expr::collect_locals(else_expr, locals_builder);
            }
            Expr::ListComprehension(ref expr, ref clauses)
            | Expr::SetComprehension(ref expr, ref clauses) => {
                Self::collect_locals_from_compr_clauses(&[expr], clauses, locals_builder);
            }
            Expr::DictComprehension((ref k, ref v), ref clauses) => {
                Self::collect_locals_from_compr_clauses(&[k, v], clauses, locals_builder);
            }
        }
    }

    fn collect_locals_from_compr_clauses(
        exprs: &[&AstExpr],
        clauses: &[AstClause],
        locals_builder: &mut LocalsBuilder,
    ) {
        match clauses.split_first() {
            Some((clause, rem)) => {
                match clause.node {
                    Clause::If(ref expr) => {
                        Expr::collect_locals(expr, locals_builder);
                    }
                    Clause::For(ref target, ref over) => {
                        Expr::collect_locals(over, locals_builder);
                        locals_builder.push_scope();
                        AssignTargetExpr::collect_locals_from_assign_expr(target, locals_builder);
                    }
                }
                Self::collect_locals_from_compr_clauses(exprs, rem, locals_builder);
                match clause.node {
                    Clause::If(..) => {}
                    Clause::For(..) => {
                        locals_builder.pop_scope();
                    }
                }
            }
            None => {
                for expr in exprs {
                    Expr::collect_locals(expr, locals_builder);
                }
            }
        }
    }
}

impl AssignTargetExpr {
    // Performing this transformation in Rust code rather than in grammar
    // to deal with ambiguous grammar.
    pub(crate) fn from_expr(
        expr: AstExpr,
    ) -> Result<AstAssignTargetExpr, lalrpop_util::ParseError<u64, lexer::Token, lexer::LexerError>>
    {
        Ok(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Identifier(ident) => AssignTargetExpr::Identifier(ident),
                Expr::ArrayIndirection(array, index) => {
                    AssignTargetExpr::ArrayIndirection(array, index)
                }
                Expr::Dot(object, field) => AssignTargetExpr::Dot(object, field),
                Expr::List(subtargets) | Expr::Tuple(subtargets) => AssignTargetExpr::Subtargets(
                    subtargets
                        .into_iter()
                        .map(AssignTargetExpr::from_expr)
                        .collect::<Result<_, _>>()?,
                ),
                _ => {
                    return Err(lalrpop_util::ParseError::User {
                        error: lexer::LexerError::WrappedError {
                            span: expr.span,
                            code: INCORRECT_ASSIGNMENT_TARGET_ERROR_CODE,
                            label: "incorrect assignment target",
                        },
                    })
                }
            },
        })
    }

    pub(crate) fn collect_locals_from_assign_expr(
        expr: &AstAssignTargetExpr,
        locals_builder: &mut LocalsBuilder,
    ) {
        match expr.node {
            AssignTargetExpr::Identifier(ref ident) => {
                locals_builder.register_local(ident.node.clone());
            }
            AssignTargetExpr::Subtargets(ref subtargets) => {
                for s in subtargets {
                    AssignTargetExpr::collect_locals_from_assign_expr(s, locals_builder);
                }
            }
            _ => {}
        }
    }
}

impl AugmentedAssignTargetExpr {
    // Performing this transformation in Rust code rather than in grammar
    // to deal with ambiguous grammar.
    pub(crate) fn from_expr(
        expr: AstExpr,
    ) -> Result<
        AstAugmentedAssignTargetExpr,
        lalrpop_util::ParseError<u64, lexer::Token, lexer::LexerError>,
    > {
        Ok(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Identifier(ident) => AugmentedAssignTargetExpr::Identifier(ident),
                Expr::ArrayIndirection(array, index) => {
                    AugmentedAssignTargetExpr::ArrayIndirection(array, index)
                }
                Expr::Dot(object, field) => AugmentedAssignTargetExpr::Dot(object, field),
                _ => {
                    return Err(lalrpop_util::ParseError::User {
                        error: lexer::LexerError::WrappedError {
                            span: expr.span,
                            code: INCORRECT_AUGMENTED_ASSIGNMENT_TARGET_ERROR_CODE,
                            label: "incorrect augmented assignment target",
                        },
                    })
                }
            },
        })
    }

    pub(crate) fn collect_locals_from_assign_expr(
        expr: &AstAugmentedAssignTargetExpr,
        locals_builder: &mut LocalsBuilder,
    ) {
        match expr.node {
            AugmentedAssignTargetExpr::Identifier(ref ident) => {
                locals_builder.register_local(ident.node.clone());
            }
            _ => {}
        }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone)]
pub enum Clause {
    For(AstAssignTargetExpr, AstExpr),
    If(AstExpr),
}
to_ast_trait!(Clause, AstClause);

#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
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
pub enum UnOp {
    Plus,
    Minus,
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnOp::Plus => write!(f, "+"),
            UnOp::Minus => write!(f, "-"),
        }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone, Copy)]
pub enum AugmentedAssignOp {
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
    Assign(AstAssignTargetExpr, AstExpr),
    AugmentedAssign(AstAugmentedAssignTargetExpr, AugmentedAssignOp, AstExpr),
    Statements(Vec<AstStatement>),
    If(AstExpr, AstStatement),
    IfElse(AstExpr, AstStatement, AstStatement),
    For(AstAssignTargetExpr, AstExpr, AstStatement),
    Def(AstString, Vec<AstParameter>, AstStatement),
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
    pub(crate) fn validate_break_continue(stmt: &AstStatement) -> Result<(), Diagnostic> {
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
            | Statement::AugmentedAssign(..)
            | Statement::Load(..) => {
                // These statements do not contain nested statements
                Ok(())
            }
        }
    }

    pub(crate) fn validate_augmented_assignment_in_module(
        stmt: &AstStatement,
    ) -> Result<(), Diagnostic> {
        match &stmt.node {
            Statement::Break
            | Statement::Continue
            | Statement::Pass
            | Statement::Return(..)
            | Statement::Expression(..)
            | Statement::Assign(..)
            | Statement::Def(..)
            | Statement::Load(..) => Ok(()),
            Statement::AugmentedAssign(target, _, _) => match &target.node {
                AugmentedAssignTargetExpr::Identifier(ident) => {
                    return Err(Diagnostic {
                        level: Level::Error,
                        message: format!(
                            "Augmented assignment is a binding \
                             and not allowed on a global variable"
                        ),
                        code: Some(AUGMENTED_ASSIGN_IN_MOD.to_owned()),
                        spans: vec![SpanLabel {
                            span: ident.span,
                            label: Some(format!("global variable")),
                            style: SpanStyle::Primary,
                        }],
                    });
                }
                _ => Ok(()),
            },
            Statement::Statements(stmts) => {
                for stmt in stmts {
                    Self::validate_augmented_assignment_in_module(stmt)?;
                }
                Ok(())
            }
            // Although top-level if and for are not allowed,
            // it's better to safer against possible future extensions
            Statement::If(_, then_block) => {
                Self::validate_augmented_assignment_in_module(then_block)?;
                Ok(())
            }
            Statement::IfElse(_, then_block, else_block) => {
                Self::validate_augmented_assignment_in_module(then_block)?;
                Self::validate_augmented_assignment_in_module(else_block)?;
                Ok(())
            }
            Statement::For(_, _, body) => Self::validate_augmented_assignment_in_module(body),
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            BinOp::EqualsTo => f.write_str("=="),
            BinOp::Different => f.write_str("!="),
            BinOp::LowerThan => f.write_str("<"),
            BinOp::GreaterThan => f.write_str(">"),
            BinOp::LowerOrEqual => f.write_str("<="),
            BinOp::GreaterOrEqual => f.write_str(">="),
            BinOp::In => f.write_str("in"),
            BinOp::NotIn => f.write_str("not in"),
            BinOp::Substraction => f.write_str("-"),
            BinOp::Addition => f.write_str("+"),
            BinOp::Multiplication => f.write_str("*"),
            BinOp::Percent => f.write_str("%"),
            BinOp::Division => f.write_str("/"),
            BinOp::FloorDivision => f.write_str("//"),
            BinOp::Pipe => f.write_str("|"),
        }
    }
}

impl Display for AugmentedAssignOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            AugmentedAssignOp::Increment => f.write_str(" += "),
            AugmentedAssignOp::Decrement => f.write_str(" += "),
            AugmentedAssignOp::Multiplier => f.write_str(" *= "),
            AugmentedAssignOp::Divider => f.write_str(" /= "),
            AugmentedAssignOp::FloorDivider => f.write_str(" //= "),
            AugmentedAssignOp::Percent => f.write_str(" %= "),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Expr::Tuple(ref e) => {
                f.write_str("(")?;
                comma_separated_fmt(f, e, |x, f| write!(f, "{}", &x.node), true)?;
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
            Expr::Identifier(ref s) => s.node.fmt(f),
            Expr::IntLiteral(ref i) => i.node.fmt(f),
            Expr::Not(ref e) => write!(f, "(not {})", e.node),
            Expr::UnOp(op, ref e) => write!(f, "{}{}", op, e.node),
            Expr::And(ref l, ref r) => write!(f, "({} and {})", l.node, r.node),
            Expr::Or(ref l, ref r) => write!(f, "({} or {})", l.node, r.node),
            Expr::BinOp(ref op, ref l, ref r) => write!(f, "({} {} {})", l.node, op, r.node),
            Expr::If(ref cond, ref v1, ref v2) => {
                write!(f, "({} if {} else {})", v1.node, cond.node, v2.node)
            }
            Expr::List(ref v) => {
                f.write_str("[")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("]")
            }
            Expr::Set(ref v) => {
                f.write_str("{")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("}")
            }
            Expr::Dict(ref v) => {
                f.write_str("{")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}: {}", x.0.node, x.1.node), false)?;
                f.write_str("}")
            }
            Expr::ListComprehension(ref e, ref v) => {
                write!(f, "[{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("]")
            }
            Expr::SetComprehension(ref e, ref v) => {
                write!(f, "{{{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("}}")
            }
            Expr::DictComprehension((ref k, ref v), ref c) => {
                write!(f, "{{{}: {}", k.node, v.node)?;
                comma_separated_fmt(f, c, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("}}")
            }
            Expr::StringLiteral(ref s) => fmt_string_literal(f, s.node.as_str()),
        }
    }
}

impl Display for AugmentedAssignTargetExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AugmentedAssignTargetExpr::Dot(object, field) => {
                write!(f, "{}.{}", object.node, field.node)
            }
            AugmentedAssignTargetExpr::ArrayIndirection(array, index) => {
                write!(f, "{}[{}]", array.node, index.node)
            }
            AugmentedAssignTargetExpr::Identifier(s) => s.node.fmt(f),
        }
    }
}

impl Display for AssignTargetExpr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AssignTargetExpr::Dot(object, field) => write!(f, "{}.{}", object.node, field.node),
            AssignTargetExpr::ArrayIndirection(array, index) => {
                write!(f, "{}[{}]", array.node, index.node)
            }
            AssignTargetExpr::Identifier(s) => s.node.fmt(f),
            AssignTargetExpr::Subtargets(subtargets) => {
                write!(f, "[")?;
                for (i, s) in subtargets.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                        s.node.fmt(f)?;
                    }
                }
                write!(f, "]")?;
                Ok(())
            }
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
    fn fmt_with_tab(&self, f: &mut dyn fmt::Write, tab: &str) -> fmt::Result {
        match *self {
            Statement::Break => writeln!(f, "{}break", tab),
            Statement::Continue => writeln!(f, "{}continue", tab),
            Statement::Pass => writeln!(f, "{}pass", tab),
            Statement::Return(Some(ref e)) => writeln!(f, "{}return {}", tab, e.node),
            Statement::Return(None) => writeln!(f, "{}return", tab),
            Statement::Expression(ref e) => writeln!(f, "{}{}", tab, e.node),
            Statement::Assign(ref l, ref r) => writeln!(f, "{}{} = {}", tab, l.node, r.node),
            Statement::AugmentedAssign(ref l, ref op, ref r) => {
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
                suite.node.fmt_with_tab(f, &indent(tab))
            }
            Statement::IfElse(ref cond, ref suite1, ref suite2) => {
                writeln!(f, "{}if {}:", tab, cond.node)?;
                suite1.node.fmt_with_tab(f, &indent(tab))?;
                writeln!(f, "{}else:", tab)?;
                suite2.node.fmt_with_tab(f, &indent(tab))
            }
            Statement::For(ref bind, ref coll, ref suite) => {
                writeln!(f, "{}for {} in {}:", tab, bind.node, coll.node)?;
                suite.node.fmt_with_tab(f, &indent(tab))
            }
            Statement::Def(ref name, ref params, ref suite) => {
                write!(f, "{}def {}(", tab, name.node)?;
                comma_separated_fmt(f, params, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("):\n")?;
                suite.node.fmt_with_tab(f, &indent(tab))
            }
            Statement::Load(ref filename, ref v) => {
                write!(f, "{}load(", tab)?;
                fmt_string_literal(f, filename.node.as_str())?;
                comma_separated_fmt(
                    f,
                    v,
                    |x, f| {
                        write!(f, "{} = ", x.0.node)?;
                        fmt_string_literal(f, x.1.node.as_str())
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
        self.fmt_with_tab(f, "")
    }
}
