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

//! Define simpler version of the evaluation function,
//! which does not support `load(...)` statement.

use crate::environment::{Environment, TypeValues, LOAD_NOT_SUPPORTED_ERROR_CODE};
use crate::eval::{EvalException, FileLoader};
use crate::syntax::dialect::Dialect;
use crate::values::Value;
use codemap::CodeMap;
use codemap_diagnostic::{Diagnostic, Level};
use std::sync::{Arc, Mutex};

/// File loader which returns error unconditionally.
pub struct NoLoadFileLoader;

impl FileLoader for NoLoadFileLoader {
    fn load(&self, _path: &str, _: &TypeValues) -> Result<Environment, EvalException> {
        Err(EvalException::DiagnosedError(Diagnostic {
            level: Level::Error,
            message: "ErrorFileLoader does not support loading".to_owned(),
            code: Some(LOAD_NOT_SUPPORTED_ERROR_CODE.to_owned()),
            spans: Vec::new(),
        }))
    }
}

/// Evaluate a string content, mutate the environment accordingly and return the evaluated value.
///
/// # Arguments
///
/// __This version uses the [`NoLoadFileLoader`] implementation for
/// the file loader__
///
/// * map: the codemap object used for diagnostics
/// * path: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate
/// * dialect: Starlark language dialect
/// * env: the environment to mutate during the evaluation
/// * global: the environment used to resolve type values
pub fn eval(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    content: &str,
    dialect: Dialect,
    env: &mut Environment,
    type_values: &TypeValues,
) -> Result<Value, Diagnostic> {
    super::eval(
        map,
        path,
        content,
        dialect,
        env,
        type_values,
        NoLoadFileLoader,
    )
}
