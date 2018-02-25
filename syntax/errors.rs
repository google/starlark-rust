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

//! Syntax error trait definition
//!
//! This module define the SyntaxError trait that all error that we pass around implements. It
//! identify all error by a unique code to identify easily an error even if changing the error
//! message.
//!
//! An error code is of the form AB00 where A is the error code level and B a module specific
//! prefix. 00 is the error number itself.
//!
//! # Error code levels:
//!
//!  * __C__ -> _Critical / Fatal_: stopped the parsing / evaluation
//!  * __E__ -> _Error_: was able to recover from the error but the state is incorrect. (e.g. a
//!  token was ignored during parsing). Prevent next phase from being run.
//!  * __W__ -> _Warning_: a warning for the user, this did not cause any error but are bad
//!  patterns that can lead to dubious behaviors.
//!  * __N__ -> _Notice_: notice of harmless improvement (e.g. dead code).
//!
//! # Modules prefix:
//!
//!  * __L__ -> Lexer
//!  * __P__ -> Parsing error
//!  * __S__ -> Syntaxic error
//!  * __E__ -> Evaluation

use codemap::Span;
use codemap_diagnostic::Diagnostic;

/// The trait that all syntax error / error linked to a location in the code must implement.
pub trait SyntaxError {
    /// Convert the error to a codemap diagnostic.
    ///
    /// To build this diagnostic, the method needs the file span corresponding to the parsed
    /// file.
    fn to_diagnostic(self, file_span: Span) -> Diagnostic;
}
