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
use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Emitter};
use environment::Environment;
use std::sync::{Arc, Mutex};
use syntax::dialect::Dialect;

/// Evaluate a string content, mutate the environment accordingly and print
/// the value of the last statement (if not `None`) or the error diagnostic. Returns true if
/// the execution succeeded, false if there were errors.
///
/// # Arguments
///
/// __This version uses the [SimpleFileLoader](SimpleFileLoader.struct.html) implementation for
/// the file loader__
///
/// * path: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate
/// * dialect: starlark language dialect
/// * env: the environment to mutate during the evaluation
pub fn eval(path: &str, content: &str, dialect: Dialect, env: &mut Environment) -> bool {
    let map = Arc::new(Mutex::new(CodeMap::new()));
    match super::simple::eval(&map, path, content, dialect, env) {
        Ok(v) => {
            if v.get_type() != "NoneType" {
                println!("{}", v.to_repr())
            };
            true
        }
        Err(p) => {
            Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
            false
        }
    }
}

/// Evaluate a file, mutate the environment accordingly and print
/// the value of the last statement (if not `None`) or the error diagnostic. Returns true if
/// the execution succeeded, false if there were errors.
///
/// __This version uses the [SimpleFileLoader](SimpleFileLoader.struct.html) implementation for
/// the file loader__
///
/// # Arguments
///
/// * path: the file to parse and evaluate
/// * dialect: Starlark language dialect
/// * env: the environment to mutate during the evaluation
pub fn eval_file(path: &str, dialect: Dialect, env: &mut Environment) -> bool {
    let map = Arc::new(Mutex::new(CodeMap::new()));
    match super::simple::eval_file(&map, path, dialect, env) {
        Ok(v) => {
            if v.get_type() != "NoneType" {
                println!("{}", v.to_repr())
            };
            true
        }
        Err(p) => {
            Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
            false
        }
    }
}
