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
use codemap::{Span, Spanned};
use lalrpop_util;
use std::collections::HashSet;
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
                                code: "CS00", // Critical Semantic 00
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
                                code: "CS01", // Critical Semantic 01
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
                                code: "CS02", // Critical Semantic 02
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
                                code: "CS03", // Critical Semantic 03
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
    Load(AstString, Vec<(AstString, AstString)>),
}
to_ast_trait!(Statement, AstStatement, Box);

macro_rules! test_param_name {
    ($argset:ident, $n:ident, $arg:ident) => {{
        if $argset.contains(&$n.node) {
            return Err(lalrpop_util::ParseError::User {
                error: lexer::LexerError::WrappedError {
                    span: $arg.span,
                    code: "CS08", // Critical Semantic 08
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
                                    code: "CS04", // Critical Semantic 04
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
                                    code: "CS05", // Critical Semantic 05
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
                                    code: "CS06", // Critical Semantic 06
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
                                    code: "CS07", // Critical Semantic 07
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
            Expr::Identifier(ref s) => s.node.fmt(f),
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
            Statement::Def(ref name, ref params, ref suite) => {
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
