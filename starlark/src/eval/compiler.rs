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

//! Utilities for translation of AST into interpreter-friendly data structures

use crate::eval::expr::AssignTargetExprCompiled;
use crate::eval::expr::AstClauseCompiled;
use crate::eval::expr::AstGlobalOrSlot;
use crate::eval::expr::ClauseCompiled;
use crate::eval::expr::ExprCompiled;
use crate::eval::expr::ExprLocal;
use crate::eval::expr::GlobalOrSlot;
use crate::eval::globals::Globals;
use crate::eval::locals::LocalsBuilder;
use crate::eval::locals::LocalsQuery;
use crate::syntax::ast::AstClause;
use crate::syntax::ast::AstExpr;
use crate::syntax::ast::AstString;
use crate::syntax::ast::Clause;
use crate::syntax::ast::Expr;
use codemap::Span;
use codemap::Spanned;
use codemap_diagnostic::Diagnostic;

/// Encapsulate differences between compilation of module scope vs
/// function or comprehension scope
pub(crate) trait LocalOrGlobalCompiler {
    /// Resolve identifier to either local slot or global name
    fn ident(&mut self, ident: AstString) -> GlobalOrSlot;

    fn ast_ident(&mut self, ident: AstString) -> AstGlobalOrSlot {
        Spanned {
            span: ident.span,
            node: self.ident(ident),
        }
    }

    /// Compile list comprehension
    fn list_comprenesion(
        &mut self,
        span: Span,
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic>;
    /// Compile set comprehension
    fn set_comprenesion(
        &mut self,
        span: Span,
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic>;
    /// Compile dict comprehension
    fn dict_comprenesion(
        &mut self,
        span: Span,
        key: AstExpr,
        value: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic>;
}

pub(crate) struct LocalCompiler<'a> {
    locals_query: &'a mut LocalsQuery<'a>,
}

impl<'a> LocalCompiler<'a> {
    pub fn new(locals_query: &'a mut LocalsQuery<'a>) -> LocalCompiler<'a> {
        LocalCompiler { locals_query }
    }
}

impl<'a> LocalCompiler<'a> {
    fn compile_clauses<R, E>(&mut self, clauses: Vec<AstClause>, expr: E) -> Result<R, Diagnostic>
    where
        E: FnOnce(Vec<AstClauseCompiled>, &mut LocalCompiler) -> Result<R, Diagnostic>,
    {
        let mut transformed_clauses = Vec::new();
        let mut scope_count = 0;
        for clause in clauses {
            transformed_clauses.push(Spanned {
                span: clause.span,
                node: match clause.node {
                    Clause::If(expr) => ClauseCompiled::If(ExprCompiled::compile(expr, self)?),
                    Clause::For(target, expr) => {
                        let expr = ExprCompiled::compile(expr, self)?;
                        self.locals_query.push_next_scope();
                        scope_count += 1;
                        let target = AssignTargetExprCompiled::compile(target, self)?;
                        ClauseCompiled::For(target, expr)
                    }
                },
            });
        }
        let r = expr(transformed_clauses, self)?;
        for _ in 0..scope_count {
            self.locals_query.pop_scope();
        }
        Ok(r)
    }
}

impl<'a> LocalOrGlobalCompiler for LocalCompiler<'a> {
    fn ident(&mut self, ident: AstString) -> GlobalOrSlot {
        let (slot, local) = self.locals_query.slot(&ident.node);
        GlobalOrSlot {
            name: ident.node,
            local,
            slot,
        }
    }

    fn list_comprenesion(
        &mut self,
        _span: Span,
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic> {
        self.compile_clauses(clauses, |clauses, compiler| {
            let expr = ExprCompiled::compile(expr, compiler)?;
            Ok(ExprCompiled::ListComprehension(expr, clauses))
        })
    }

    fn set_comprenesion(
        &mut self,
        _span: Span,
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic> {
        self.compile_clauses(clauses, |clauses, compiler| {
            let expr = ExprCompiled::compile(expr, compiler)?;
            Ok(ExprCompiled::SetComprehension(expr, clauses))
        })
    }

    fn dict_comprenesion(
        &mut self,
        _span: Span,
        key: AstExpr,
        value: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic> {
        self.compile_clauses(clauses, |clauses, compiler| {
            let key = ExprCompiled::compile(key, compiler)?;
            let value = ExprCompiled::compile(value, compiler)?;
            Ok(ExprCompiled::DictComprehension((key, value), clauses))
        })
    }
}

pub(crate) struct GlobalCompiler<'a> {
    globals: &'a mut Globals,
}

impl<'a> GlobalCompiler<'a> {
    pub fn new(globals: &'a mut Globals) -> GlobalCompiler<'a> {
        GlobalCompiler { globals }
    }

    fn compile_comprehension_in_global_scope(
        &mut self,
        expr: AstExpr,
    ) -> Result<ExprCompiled, Diagnostic> {
        let mut locals_builder = LocalsBuilder::default();

        Expr::collect_locals(&expr, &mut locals_builder);

        let locals = locals_builder.build();
        // Note we are using private global index for comprehensions
        let mut globals = Globals::default();

        let mut locals_query = LocalsQuery::new(&locals, &mut globals);

        let expr = ExprCompiled::compile_local(expr, &mut locals_query)?;

        Ok(ExprCompiled::Local(ExprLocal {
            expr,
            locals,
            globals,
        }))
    }
}

impl<'a> LocalOrGlobalCompiler for GlobalCompiler<'a> {
    fn ident(&mut self, ident: AstString) -> GlobalOrSlot {
        GlobalOrSlot {
            slot: self.globals.register_global(&ident.node),
            name: ident.node,
            local: false,
        }
    }
    fn list_comprenesion(
        &mut self,
        span: Span,
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic> {
        self.compile_comprehension_in_global_scope(Box::new(Spanned {
            span,
            node: Expr::ListComprehension(expr, clauses),
        }))
    }

    fn set_comprenesion(
        &mut self,
        span: Span,
        expr: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic> {
        self.compile_comprehension_in_global_scope(Box::new(Spanned {
            span,
            node: Expr::SetComprehension(expr, clauses),
        }))
    }

    fn dict_comprenesion(
        &mut self,
        span: Span,
        key: AstExpr,
        value: AstExpr,
        clauses: Vec<AstClause>,
    ) -> Result<ExprCompiled, Diagnostic> {
        self.compile_comprehension_in_global_scope(Box::new(Spanned {
            span,
            node: Expr::DictComprehension((key, value), clauses),
        }))
    }
}
