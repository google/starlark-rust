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

use codemap::{Span, Spanned};
use std::fmt;
use std::collections::HashSet;
use super::lexer;
extern crate lalrpop_util;

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
    ($t1: ty, $t2: ty, $t3: ident) => (
        impl ToAst<$t2> for $t1 {
            fn to_ast(self, span: Span) -> $t2 { $t3::new(Spanned { span, node: self }) }
        }
    );
    ($t1: ty, $t2: ty) => (
        impl ToAst<$t2> for $t1 {
            fn to_ast(self, span: Span) -> $t2 { Spanned { span, node: self } }
        }
    )
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
    Call(AstExpr, Vec<AstExpr>, Vec<(AstString, AstExpr)>, Option<AstExpr>, Option<AstExpr>),
    ArrayIndirection(AstExpr, AstExpr),
    Slice(AstExpr, Option<AstExpr>, Option<AstExpr>, Option<AstExpr>),
    Identifier(AstString),
    IntLitteral(AstInt),
    StringLitteral(AstString),
    Not(AstExpr),
    Minus(AstExpr),
    Plus(AstExpr),
    Op(BinOp, AstExpr, AstExpr),
    If(AstExpr, AstExpr, AstExpr), // Order: condition, v1, v2 <=> v1 if condition else v2
    List(Vec<AstExpr>),
    Dict(Vec<(AstExpr, AstExpr)>),
    ListComprehension(AstExpr, Vec<AstClause>),
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
    For(AstClause, AstStatement),
    Def(AstString, Vec<AstParameter>, AstStatement),
    Load(AstString, Vec<(AstString, AstString)>),
}
to_ast_trait!(Statement, AstStatement, Box);

macro_rules! test_param_name {
    ($argset:ident, $n: ident, $arg: ident) => (
        {
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
        }
    )
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
            for ref arg in parameters.iter() {
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
                                    label: "Default parameter after args array or kwargs dictionary",
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

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            BinOp::Or => write!(f, " or "),
            BinOp::And => write!(f, " and "),
            BinOp::EqualsTo => write!(f, " == "),
            BinOp::Different => write!(f, " != "),
            BinOp::LowerThan => write!(f, " < "),
            BinOp::GreaterThan => write!(f, " > "),
            BinOp::LowerOrEqual => write!(f, " <= "),
            BinOp::GreaterOrEqual => write!(f, " >= "),
            BinOp::In => write!(f, " in "),
            BinOp::NotIn => write!(f, " not in "),
            BinOp::Substraction => write!(f, " - "),
            BinOp::Addition => write!(f, " + "),
            BinOp::Multiplication => write!(f, " * "),
            BinOp::Percent => write!(f, " % "),
            BinOp::Division => write!(f, " / "),
            BinOp::Pipe => write!(f, " | "),
        }
    }
}

impl fmt::Display for AssignOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            AssignOp::Assign => write!(f, " = "),
            AssignOp::Increment => write!(f, " += "),
            AssignOp::Decrement => write!(f, " += "),
            AssignOp::Multiplier => write!(f, " *= "),
            AssignOp::Divider => write!(f, " /= "),
            AssignOp::Percent => write!(f, " %= "),
        }
    }
}

fn comma_separated_fmt<I, F>(
    f: &mut fmt::Formatter,
    v: &Vec<I>,
    converter: F,
    for_tuple: bool,
) -> fmt::Result
where
    F: Fn(&I, &mut fmt::Formatter) -> fmt::Result,
{
    for (i, e) in v.iter().enumerate() {
        let sep = if i == 0 { "" } else { ", " };
        write!(f, "{}", sep)?;
        converter(e, f)?;
    }
    if v.len() == 1 && for_tuple {
        write!(f, ",")?;
    }
    Ok(())
}

fn fmt_string_litteral(f: &mut fmt::Formatter, s: &str) -> fmt::Result {
    write!(f, "\"")?;
    for c in s.chars() {
        match c {
            '\n' => write!(f, "\\n")?,
            '\t' => write!(f, "\\t")?,
            '\r' => write!(f, "\\r")?,
            '\0' => write!(f, "\\0")?,
            '"' => write!(f, "\\\"")?,
            '\\' => write!(f, "\\\\")?,
            x => write!(f, "{}", x)?,
        }
    }
    write!(f, "\"")
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Expr::Tuple(ref e) => {
                write!(f, "(")?;
                comma_separated_fmt(f, e, |x, f| write!(f, "{}", x.node), true)?;
                write!(f, ")")
            }
            Expr::Dot(ref e, ref s) => write!(f, "{}.{}", e.node, s.node),
            Expr::Call(ref e, ref pos, ref named, ref args, ref kwargs) => {
                write!(f, "{}(", e.node)?;
                let mut first = true;
                for ref a in pos {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{}", a.node)?;
                }
                for &(ref k, ref v) in named {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "{} = {}", k.node, v.node)?;
                }
                if let &Some(ref x) = args {
                    if !first {
                        write!(f, ", ")?;
                    }
                    first = false;
                    write!(f, "*{}", x.node)?;
                }
                if let &Some(ref x) = kwargs {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "**{}", x.node)?;
                }
                write!(f, ")")
            }
            Expr::ArrayIndirection(ref e, ref i) => write!(f, "{}[{}]", e.node, i.node),
            Expr::Slice(ref e, ref i1, ref i2, ref i3) => {
                write!(f, "{}[]", e.node)?;
                if let &Some(ref x) = i1 {
                    write!(f, "{}:", x.node)?
                } else {
                    write!(f, ":")?
                }
                if let &Some(ref x) = i2 {
                    write!(f, "{}", x.node)?
                }
                if let &Some(ref x) = i3 {
                    write!(f, ":{}", x.node)?
                }
                Ok(())
            }
            Expr::Identifier(ref s) => write!(f, "{}", s.node),
            Expr::IntLitteral(ref i) => write!(f, "{}", i.node),
            Expr::Not(ref e) => write!(f, "(not {})", e.node),
            Expr::Minus(ref e) => write!(f, "-{}", e.node),
            Expr::Plus(ref e) => write!(f, "+{}", e.node),
            Expr::Op(ref op, ref l, ref r) => write!(f, "({}{}{})", l.node, op, r.node),
            Expr::If(ref cond, ref v1, ref v2) => {
                write!(f, "({} if {} else {})", v1.node, cond.node, v2.node)
            }
            Expr::List(ref v) => {
                write!(f, "[")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", x.node), false)?;
                write!(f, "]")
            }
            Expr::Dict(ref v) => {
                write!(f, "{{")?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}: {}", x.0.node, x.1.node), false)?;
                write!(f, "}}")
            }
            Expr::ListComprehension(ref e, ref v) => {
                write!(f, "[{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", x.node), false)?;
                write!(f, "]")
            }
            Expr::DictComprehension((ref k, ref v), ref c) => {
                write!(f, "{{{}: {}", k.node, v.node)?;
                comma_separated_fmt(f, c, |x, f| write!(f, "{}", x.node), false)?;
                write!(f, "}}")
            }
            Expr::StringLitteral(ref s) => fmt_string_litteral(f, &s.node),
        }
    }
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Argument::Positional(ref s) => write!(f, "{}", s.node),
            Argument::Named(ref s, ref e) => write!(f, "{} = {}", s.node, e.node),
            Argument::ArgsArray(ref s) => write!(f, "*{}", s.node),
            Argument::KWArgsDict(ref s) => write!(f, "**{}", s.node),
        }
    }
}

impl fmt::Display for Parameter {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Parameter::Normal(ref s) => write!(f, "{}", s.node),
            Parameter::WithDefaultValue(ref s, ref e) => write!(f, "{} = {}", s.node, e.node),
            Parameter::Args(ref s) => write!(f, "*{}", s.node),
            Parameter::KWArgs(ref s) => write!(f, "**{}", s.node),
        }
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Clause::For(ref t, ref e) => write!(f, " for {} in {}", t.node, e.node),
            Clause::If(ref t) => write!(f, " if {}", t.node),
        }
    }
}

impl Statement {
    fn fmt_with_tab(&self, f: &mut fmt::Formatter, tab: String) -> fmt::Result {
        match *self {
            Statement::Break => write!(f, "{}break\n", tab),
            Statement::Continue => write!(f, "{}continue\n", tab),
            Statement::Pass => write!(f, "{}pass\n", tab),
            Statement::Return(Some(ref e)) => write!(f, "{}return {}\n", tab, e.node),
            Statement::Return(None) => write!(f, "{}return\n", tab),
            Statement::Expression(ref e) => write!(f, "{}{}\n", tab, e.node),
            Statement::Assign(ref l, ref op, ref r) => {
                write!(f, "{}{}{}{}\n", tab, l.node, op, r.node)
            }
            Statement::Statements(ref v) => {
                for s in v {
                    s.node.fmt_with_tab(f, tab.clone())?;
                }
                Ok(())
            }
            Statement::If(ref cond, ref suite) => {
                write!(f, "{}if {}:\n", tab, cond.node)?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::IfElse(ref cond, ref suite1, ref suite2) => {
                write!(f, "{}if {}:\n", tab, cond.node)?;
                suite1.node.fmt_with_tab(f, tab.clone() + "  ")?;
                write!(f, "{}else:\n", tab)?;
                suite2.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::For(ref clause, ref suite) => {
                write!(f, "{}for {}:\n", tab, clause.node)?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::Def(ref name, ref params, ref suite) => {
                write!(f, "{}def {}(", tab, name.node)?;
                comma_separated_fmt(f, params, |x, f| write!(f, "{}", x.node), false)?;
                write!(f, "):\n")?;
                suite.node.fmt_with_tab(f, tab + "  ")
            }
            Statement::Load(ref filename, ref v) => {
                write!(f, "{}load(", tab)?;
                fmt_string_litteral(f, &filename.node)?;
                comma_separated_fmt(
                    f,
                    v,
                    |x, f| {
                        write!(f, "{} = ", x.0.node)?;
                        fmt_string_litteral(f, &(x.1.node))
                    },
                    false,
                )?;
                write!(f, ")\n")
            }
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_with_tab(f, "".to_owned())
    }
}
