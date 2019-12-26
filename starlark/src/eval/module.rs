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

//! Starlark module (`.bzl` or `BUILD` file parsed and post-processed)

use crate::eval::globals::Globals;
use crate::eval::stmt::BlockCompiled;
use crate::syntax::ast::AstStatement;
use crate::syntax::ast::Statement;
use crate::syntax::dialect::Dialect;
use codemap_diagnostic::Diagnostic;

/// Starlark module (`.bzl` or `BUILD` file parsed and post-processed)
#[derive(Debug, Clone)]
pub struct Module {
    /// Index of global variables used in this scope
    /// (but not in child scopes).
    pub(crate) globals: Globals,
    /// Code
    pub(crate) block: BlockCompiled,
}

impl Module {
    pub(crate) fn compile(stmt: AstStatement, _dialect: Dialect) -> Result<Module, Diagnostic> {
        let mut globals = Globals::default();
        Statement::validate_break_continue(&stmt)?;
        Statement::validate_augmented_assignment_in_module(&stmt)?;
        let block = BlockCompiled::compile_global(stmt, &mut globals)?;
        Ok(Module { globals, block })
    }
}
