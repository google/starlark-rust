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

//! Interpreter-ready expr

use crate::eval::compiler::GlobalCompiler;
use crate::eval::compiler::LocalCompiler;
use crate::eval::compiler::LocalOrGlobalCompiler;
use crate::eval::globals::Globals;
use crate::eval::locals::Locals;
use crate::eval::locals::LocalsQuery;
use crate::stdlib::structs::StarlarkStruct;
use crate::syntax::ast::AssignTargetExpr;
use crate::syntax::ast::AstAssignTargetExpr;
use crate::syntax::ast::AstAugmentedAssignTargetExpr;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::AstString;
use crate::syntax::ast::AugmentedAssignTargetExpr;
use crate::syntax::ast::BinOp;
use crate::syntax::ast::Expr;
use crate::syntax::ast::UnOp;
use crate::syntax::fmt::comma_separated_fmt;
use crate::values::frozen::FrozenValue;
use crate::values::inspect::Inspectable;
use crate::values::string::rc::RcString;
use crate::values::Value;
use codemap::Spanned;
use codemap_diagnostic::Diagnostic;
use linked_hash_map::LinkedHashMap;
use std::fmt;

/// After syntax check each variable is resolved to either global or slot
#[derive(Debug, Clone)]
pub(crate) struct GlobalOrSlot {
    pub name: RcString,
    pub local: bool,
    pub slot: usize,
}
pub(crate) type AstGlobalOrSlot = Spanned<GlobalOrSlot>;

#[derive(Debug, Clone)]
pub(crate) enum AssignTargetExprCompiled {
    Name(AstGlobalOrSlot),
    Dot(AstExprCompiled, AstString),
    ArrayIndirection(AstExprCompiled, AstExprCompiled),
    Subtargets(Vec<AstAssignTargetExprCompiled>),
}
pub(crate) type AstAssignTargetExprCompiled = Spanned<AssignTargetExprCompiled>;

#[derive(Debug, Clone)]
pub(crate) enum AugmentedAssignTargetExprCompiled {
    // there's no augmented assignment for globals
    Slot(usize, AstString),
    Dot(AstExprCompiled, AstString),
    ArrayIndirection(AstExprCompiled, AstExprCompiled),
}
pub(crate) type AstAugmentedAssignTargetExprCompiled = Spanned<AugmentedAssignTargetExprCompiled>;

impl fmt::Display for AugmentedAssignTargetExprCompiled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AugmentedAssignTargetExprCompiled::Slot(_, s) => write!(f, "{}", s.node),
            AugmentedAssignTargetExprCompiled::Dot(object, field) => {
                write!(f, "{}.{}", object.node, field.node)
            }
            AugmentedAssignTargetExprCompiled::ArrayIndirection(array, index) => {
                write!(f, "{}[{}]", array.node, index.node)
            }
        }
    }
}

#[doc(hidden)]
#[derive(Debug, Clone)]
pub(crate) enum ClauseCompiled {
    For(AstAssignTargetExprCompiled, AstExprCompiled),
    If(AstExprCompiled),
}
pub(crate) type AstClauseCompiled = Spanned<ClauseCompiled>;

impl fmt::Display for ClauseCompiled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            ClauseCompiled::For(ref t, ref e) => write!(f, " for {} in {}", t.node, e.node),
            ClauseCompiled::If(ref t) => write!(f, " if {}", t.node),
        }
    }
}

/// Expression wrapper which creates own local context.
/// Used to evaluate comprehensions
#[derive(Debug, Clone)]
pub(crate) struct ExprLocal {
    pub expr: AstExprCompiled,
    pub locals: Locals,
    pub globals: Globals,
}

impl Inspectable for ExprLocal {
    fn inspect(&self) -> Value {
        let mut fields = LinkedHashMap::<RcString, Value>::new();
        fields.insert("expr".into(), self.expr.inspect());
        fields.insert("locals".into(), self.locals.inspect());
        fields.insert("globals".into(), self.globals.inspect());
        Value::new(StarlarkStruct::new(fields))
    }
}

/// Interperter-ready version of [`Expr`](crate::syntax::ast::Expr)
#[derive(Debug, Clone)]
pub(crate) enum ExprCompiled {
    Tuple(Vec<AstExprCompiled>),
    Dot(AstExprCompiled, AstString),
    Call(
        AstExprCompiled,
        Vec<AstExprCompiled>,
        Vec<(AstString, AstExprCompiled)>,
        Option<AstExprCompiled>,
        Option<AstExprCompiled>,
    ),
    ArrayIndirection(AstExprCompiled, AstExprCompiled),
    Slice(
        AstExprCompiled,
        Option<AstExprCompiled>,
        Option<AstExprCompiled>,
        Option<AstExprCompiled>,
    ),
    Name(AstGlobalOrSlot),
    Value(FrozenValue),
    Not(AstExprCompiled),
    And(AstExprCompiled, AstExprCompiled),
    Or(AstExprCompiled, AstExprCompiled),
    BinOp(BinOp, AstExprCompiled, AstExprCompiled),
    UnOp(UnOp, AstExprCompiled),
    If(AstExprCompiled, AstExprCompiled, AstExprCompiled), // Order: condition, v1, v2 <=> v1 if condition else v2
    List(Vec<AstExprCompiled>),
    Set(Vec<AstExprCompiled>),
    Dict(Vec<(AstExprCompiled, AstExprCompiled)>),
    ListComprehension(AstExprCompiled, Vec<AstClauseCompiled>),
    SetComprehension(AstExprCompiled, Vec<AstClauseCompiled>),
    DictComprehension((AstExprCompiled, AstExprCompiled), Vec<AstClauseCompiled>),
    /// Creates a local scope for evaluation of subexpression in global scope.
    /// Used for evaluate comprehensions in global scope.
    Local(ExprLocal),
}

impl fmt::Display for ExprCompiled {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExprCompiled::Tuple(t) => {
                write!(f, "(")?;
                comma_separated_fmt(f, &t, |x, f| write!(f, "{}", &x.node), true)?;
                write!(f, ")")
            }
            ExprCompiled::List(l) => {
                write!(f, "[")?;
                comma_separated_fmt(f, &l, |x, f| write!(f, "{}", &x.node), false)?;
                write!(f, "]")
            }
            ExprCompiled::Set(s) => {
                write!(f, "{{")?;
                comma_separated_fmt(f, &s, |x, f| write!(f, "{}", &x.node), false)?;
                write!(f, "}}")
            }
            ExprCompiled::Dict(d) => {
                write!(f, "{{")?;
                comma_separated_fmt(
                    f,
                    &d,
                    |x, f| write!(f, "{}: {}", &x.0.node, &x.1.node),
                    false,
                )?;
                write!(f, "}}")
            }
            ExprCompiled::Dot(object, field) => write!(f, "{}.{}", object.node, field.node),
            ExprCompiled::ArrayIndirection(array, index) => {
                write!(f, "{}[{}]", array.node, index.node)
            }
            ExprCompiled::Slice(array, a, b, c) => {
                write!(f, "{}[", array.node)?;
                if let Some(a) = a {
                    write!(f, "{}", a.node)?;
                }
                write!(f, ":")?;
                if let Some(b) = b {
                    write!(f, "{}", b.node)?;
                }
                write!(f, ":")?;
                if let Some(c) = c {
                    write!(f, "{}", c.node)?;
                }
                write!(f, "]")
            }
            ExprCompiled::Name(name) => write!(f, "{}", name.name),
            ExprCompiled::Value(v) => write!(f, "{}", v),
            ExprCompiled::Not(expr) => write!(f, "not {}", expr.node),
            ExprCompiled::UnOp(op, expr) => write!(f, "{}{}", op, expr.node),
            ExprCompiled::And(l, r) => write!(f, "{} and {}", l.node, r.node),
            ExprCompiled::Or(l, r) => write!(f, "{} or {}", l.node, r.node),
            ExprCompiled::BinOp(op, l, r) => write!(f, "{} {} {}", l.node, op, r.node),
            ExprCompiled::If(cond, th, el) => {
                write!(f, "{} if {} else {}", th.node, cond.node, el.node)
            }
            ExprCompiled::Call(e, pos, named, args, kwargs) => {
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
            ExprCompiled::ListComprehension(ref e, ref v) => {
                write!(f, "[{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("]")
            }
            ExprCompiled::SetComprehension(ref e, ref v) => {
                write!(f, "{{{}", e.node)?;
                comma_separated_fmt(f, v, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("}}")
            }
            ExprCompiled::DictComprehension((ref k, ref v), ref c) => {
                write!(f, "{{{}: {}", k.node, v.node)?;
                comma_separated_fmt(f, c, |x, f| write!(f, "{}", &x.node), false)?;
                f.write_str("}}")
            }
            ExprCompiled::Local(local) => write!(f, "{}", local.expr.node),
        }
    }
}

#[doc(hidden)]
pub(crate) type AstExprCompiled = Box<Spanned<ExprCompiled>>;

impl GlobalOrSlot {
    pub fn inspect(&self) -> Value {
        let GlobalOrSlot { name, local, slot } = self;
        Value::from((name.clone(), if *local { "local" } else { "global" }, *slot))
    }
}

impl ExprCompiled {
    pub(crate) fn compile<C: LocalOrGlobalCompiler>(
        expr: AstExpr,
        compiler: &mut C,
    ) -> Result<AstExprCompiled, Diagnostic> {
        Ok(Box::new(Spanned {
            span: expr.span,
            node: match expr.node {
                Expr::Tuple(args) => ExprCompiled::Tuple(
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::List(args) => ExprCompiled::List(
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Set(args) => ExprCompiled::Set(
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Dict(args) => ExprCompiled::Dict(
                    args.into_iter()
                        .map(|(k, v)| {
                            Ok((Self::compile(k, compiler)?, Self::compile(v, compiler)?))
                        })
                        .collect::<Result<_, _>>()?,
                ),
                Expr::Identifier(ident) => ExprCompiled::Name(Spanned {
                    span: ident.span,
                    node: compiler.ident(ident),
                }),
                Expr::Dot(object, field) => {
                    ExprCompiled::Dot(Self::compile(object, compiler)?, field)
                }
                Expr::ArrayIndirection(array, index) => ExprCompiled::ArrayIndirection(
                    Self::compile(array, compiler)?,
                    Self::compile(index, compiler)?,
                ),
                Expr::Call(f, args, kwargs, star, star_star) => ExprCompiled::Call(
                    Self::compile(f, compiler)?,
                    args.into_iter()
                        .map(|a| Self::compile(a, compiler))
                        .collect::<Result<_, _>>()?,
                    kwargs
                        .into_iter()
                        .map(|(k, v)| Ok((k, Self::compile(v, compiler)?)))
                        .collect::<Result<_, _>>()?,
                    star.map(|e| Self::compile(e, compiler)).transpose()?,
                    star_star.map(|e| Self::compile(e, compiler)).transpose()?,
                ),
                Expr::Slice(array, a, b, c) => ExprCompiled::Slice(
                    Self::compile(array, compiler)?,
                    a.map(|e| Self::compile(e, compiler)).transpose()?,
                    b.map(|e| Self::compile(e, compiler)).transpose()?,
                    c.map(|e| Self::compile(e, compiler)).transpose()?,
                ),
                Expr::IntLiteral(i) => ExprCompiled::Value(FrozenValue::from(i.node)),
                Expr::StringLiteral(s) => {
                    ExprCompiled::Value(FrozenValue::new(s.node.into()).unwrap())
                }
                Expr::Not(e) => ExprCompiled::Not(Self::compile(e, compiler)?),
                Expr::And(lhs, rhs) => {
                    ExprCompiled::And(Self::compile(lhs, compiler)?, Self::compile(rhs, compiler)?)
                }
                Expr::Or(lhs, rhs) => {
                    ExprCompiled::Or(Self::compile(lhs, compiler)?, Self::compile(rhs, compiler)?)
                }
                Expr::BinOp(op, lhs, rhs) => ExprCompiled::BinOp(
                    op,
                    Self::compile(lhs, compiler)?,
                    Self::compile(rhs, compiler)?,
                ),
                Expr::UnOp(op, e) => ExprCompiled::UnOp(op, Self::compile(e, compiler)?),
                Expr::If(cond, then_expr, else_expr) => ExprCompiled::If(
                    Self::compile(cond, compiler)?,
                    Self::compile(then_expr, compiler)?,
                    Self::compile(else_expr, compiler)?,
                ),
                Expr::ListComprehension(expr, clauses) => {
                    compiler.list_comprenesion(expr.span, expr, clauses)?
                }
                Expr::SetComprehension(expr, clauses) => {
                    compiler.set_comprenesion(expr.span, expr, clauses)?
                }
                Expr::DictComprehension((key, value), clauses) => {
                    compiler.dict_comprenesion(expr.span, key, value, clauses)?
                }
            },
        }))
    }

    pub(crate) fn compile_local<'a>(
        expr: AstExpr,
        locals_query: &'a mut LocalsQuery<'a>,
    ) -> Result<AstExprCompiled, Diagnostic> {
        Self::compile(expr, &mut LocalCompiler::new(locals_query))
    }

    pub(crate) fn compile_global(
        expr: AstExpr,
        globals: &mut Globals,
    ) -> Result<AstExprCompiled, Diagnostic> {
        Self::compile(expr, &mut GlobalCompiler::new(globals))
    }
}

impl Inspectable for ExprCompiled {
    fn inspect(&self) -> Value {
        let (name, param): (&str, Value) = match &self {
            ExprCompiled::Dot(object, field) => ("dot", (object.inspect(), field.inspect()).into()),
            ExprCompiled::ArrayIndirection(array, index) => (
                "array_indirection",
                (array.inspect(), index.inspect()).into(),
            ),
            ExprCompiled::Call(expr, args, kwargs, star, star_star) => {
                ("call", (expr, args, kwargs, star, star_star).inspect())
            }
            ExprCompiled::Slice(array, a, b, c) => ("slice", (array, a, b, c).inspect()),
            ExprCompiled::Name(n) => ("name", n.node.inspect()),
            ExprCompiled::Value(v) => ("value", Value::from(v.clone())),
            ExprCompiled::Not(e) => ("not", e.inspect()),
            ExprCompiled::And(l, r) => ("and", (l, r).inspect()),
            ExprCompiled::Or(l, r) => ("or", (l, r).inspect()),
            ExprCompiled::BinOp(op, l, r) => ("bin_op", (format!("{:?}", op), l, r).inspect()),
            ExprCompiled::UnOp(op, e) => ("un_op", (format!("{:?}", op), e).inspect()),
            ExprCompiled::If(cond, then_expr, else_expr) => {
                ("if", (cond, then_expr, else_expr).inspect())
            }
            ExprCompiled::List(e) => ("list", e.inspect()),
            ExprCompiled::Tuple(e) => ("tuple", e.inspect()),
            ExprCompiled::Set(e) => ("set", e.inspect()),
            ExprCompiled::Dict(d) => ("dict", d.inspect()),
            ExprCompiled::ListComprehension(expr, clauses) => {
                ("list_comprehension", (expr, clauses).inspect())
            }
            ExprCompiled::DictComprehension(expr, clauses) => {
                ("dict_comprehension", (expr, clauses).inspect())
            }
            ExprCompiled::SetComprehension(expr, clauses) => {
                ("set_comprehension", (expr, clauses).inspect())
            }
            ExprCompiled::Local(e) => ("local", e.inspect()),
        };
        Value::from((Value::from(name), param))
    }
}

impl AssignTargetExprCompiled {
    pub(crate) fn compile<C: LocalOrGlobalCompiler>(
        expr: AstAssignTargetExpr,
        compiler: &mut C,
    ) -> Result<AstAssignTargetExprCompiled, Diagnostic> {
        Ok(Spanned {
            span: expr.span,
            node: match expr.node {
                AssignTargetExpr::Identifier(a) => {
                    AssignTargetExprCompiled::Name(compiler.ast_ident(a))
                }
                AssignTargetExpr::ArrayIndirection(array, index) => {
                    AssignTargetExprCompiled::ArrayIndirection(
                        ExprCompiled::compile(array, compiler)?,
                        ExprCompiled::compile(index, compiler)?,
                    )
                }
                AssignTargetExpr::Dot(object, field) => {
                    AssignTargetExprCompiled::Dot(ExprCompiled::compile(object, compiler)?, field)
                }
                AssignTargetExpr::Subtargets(subtargets) => AssignTargetExprCompiled::Subtargets(
                    subtargets
                        .into_iter()
                        .map(|t| AssignTargetExprCompiled::compile(t, compiler))
                        .collect::<Result<_, _>>()?,
                ),
            },
        })
    }
}

impl AugmentedAssignTargetExprCompiled {
    pub(crate) fn compile_impl<C: LocalOrGlobalCompiler>(
        expr: AstAugmentedAssignTargetExpr,
        compiler: &mut C,
    ) -> Result<AstAugmentedAssignTargetExprCompiled, Diagnostic> {
        Ok(Spanned {
            span: expr.span,
            node: match expr.node {
                AugmentedAssignTargetExpr::Identifier(a) => {
                    let span = a.span;
                    let GlobalOrSlot { slot, local, name } = compiler.ident(a);
                    assert!(local, "global must be filtered out at parse level");
                    AugmentedAssignTargetExprCompiled::Slot(slot, Spanned { span, node: name })
                }
                AugmentedAssignTargetExpr::ArrayIndirection(array, index) => {
                    AugmentedAssignTargetExprCompiled::ArrayIndirection(
                        ExprCompiled::compile(array, compiler)?,
                        ExprCompiled::compile(index, compiler)?,
                    )
                }
                AugmentedAssignTargetExpr::Dot(object, field) => {
                    AugmentedAssignTargetExprCompiled::Dot(
                        ExprCompiled::compile(object, compiler)?,
                        field,
                    )
                }
            },
        })
    }
}

impl Inspectable for AssignTargetExprCompiled {
    fn inspect(&self) -> Value {
        let (name, param): (&str, Value) = match self {
            AssignTargetExprCompiled::Dot(object, field) => ("dot", (object, field).inspect()),
            AssignTargetExprCompiled::ArrayIndirection(array, index) => {
                ("array_indirection", (array, index).inspect())
            }
            AssignTargetExprCompiled::Name(name) => ("name", name.node.inspect()),
            AssignTargetExprCompiled::Subtargets(st) => ("subtargets", st.inspect()),
        };
        Value::from((name, param))
    }
}

impl Inspectable for AugmentedAssignTargetExprCompiled {
    fn inspect(&self) -> Value {
        let (name, param): (&str, Value) = match self {
            AugmentedAssignTargetExprCompiled::Slot(slot, name) => ("slot", (slot, name).inspect()),
            AugmentedAssignTargetExprCompiled::ArrayIndirection(array, index) => {
                ("array_indirection", (array, index).inspect())
            }
            AugmentedAssignTargetExprCompiled::Dot(object, field) => {
                ("dot", (object, field).inspect())
            }
        };
        Value::from((name, param))
    }
}

impl Inspectable for ClauseCompiled {
    fn inspect(&self) -> Value {
        let (name, param): (&str, Value) = match self {
            ClauseCompiled::If(cond) => ("if", cond.inspect()),
            ClauseCompiled::For(var, over) => ("for", (var, over).inspect()),
        };
        Value::from((name, param))
    }
}
