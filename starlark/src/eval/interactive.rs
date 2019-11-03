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

//! Defines very basic versions of the evaluation functions that are suitable for interactive use:
//! they output diagnostic to stderr and the result value to stdout.
use crate::environment::{Environment, TypeValues};
use crate::syntax::dialect::Dialect;
use crate::values::Value;
use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use std::sync::{Arc, Mutex};

pub struct EvalError {
    codemap: Arc<Mutex<CodeMap>>,
    diagnostic: Diagnostic,
}

impl EvalError {
    pub fn write_to_stderr(self) {
        Emitter::stderr(ColorConfig::Auto, Some(&self.codemap.lock().unwrap()))
            .emit(&[self.diagnostic])
    }
}

/// Evaluate a string content, mutate the environment accordingly, and return the value of the last
/// statement, or a printable error.
///
/// # Arguments
///
/// __This version uses the [`SimpleFileLoader`](crate::eval::simple::SimpleFileLoader)
/// implementation for the file loader__
///
/// * path: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate
/// * dialect: starlark language dialect
/// * env: the environment to mutate during the evaluation
pub fn eval(
    path: &str,
    content: &str,
    dialect: Dialect,
    env: &mut Environment,
    type_values: &TypeValues,
    file_loader_env: Environment,
) -> Result<Option<Value>, EvalError> {
    let map = Arc::new(Mutex::new(CodeMap::new()));
    transform_result(
        super::simple::eval(
            &map,
            path,
            content,
            dialect,
            env,
            type_values,
            file_loader_env,
        ),
        map,
    )
}

/// Evaluate a file, mutate the environment accordingly, and return the value of the last
/// statement, or a printable error.
///
/// __This version uses the [`SimpleFileLoader`](crate::eval::simple::SimpleFileLoader)
/// implementation for the file loader__
///
/// # Arguments
///
/// * path: the file to parse and evaluate
/// * dialect: Starlark language dialect
/// * env: the environment to mutate during the evaluation
pub fn eval_file(
    path: &str,
    dialect: Dialect,
    env: &mut Environment,
    type_values: &TypeValues,
    file_loader_env: Environment,
) -> Result<Option<Value>, EvalError> {
    let map = Arc::new(Mutex::new(CodeMap::new()));
    transform_result(
        super::simple::eval_file(&map, path, dialect, env, type_values, file_loader_env),
        map,
    )
}

fn transform_result(
    result: Result<Value, Diagnostic>,
    codemap: Arc<Mutex<CodeMap>>,
) -> Result<Option<Value>, EvalError> {
    match result {
        Ok(ref v) if v.get_type() == "NoneType" => Ok(None),
        Ok(v) => Ok(Some(v)),
        Err(diagnostic) => Err(EvalError {
            codemap,
            diagnostic,
        }),
    }
}
