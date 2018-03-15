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

//! Macro to test starlark code execution
use environment;
use std::sync;
use codemap::CodeMap;
use codemap_diagnostic::{Diagnostic, Emitter, ColorConfig};
use values::TypedValue;
use eval;

/// Execute a starlark snippet with an empty environment.
pub fn starlark_empty(snippet: &str) -> Result<bool, Diagnostic> {
    let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
    let mut env = environment::Environment::new("test");
    match eval::simple::eval(&map, "<test>", snippet, false, &mut env) {
        Ok(v) => Ok(v.to_bool()),
        Err(d) => {
            Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[d.clone()]);
            Err(d)
        }
    }
}

/// Execute a starlark snippet with an empty environment.
pub fn starlark_empty_no_diagnostic(snippet: &str) -> Result<bool, Diagnostic> {
    let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
    let mut env = environment::Environment::new("test");
    Ok(eval::simple::eval(&map, "<test>", snippet, false, &mut env)?.to_bool())
}

/// A simple macro to execute a Starlark snippet and fails if the last statement is false.
macro_rules! starlark_ok_fn {
    ($fn: path, $t:expr) => (
        assert!($fn($t).unwrap());
    );
    ($fn: path, $t1:expr, $t2:expr) => (
        assert!($fn(&format!("{}{}", $t1, $t2)).unwrap());
    );
}

/// Test that the execution of a starlark code raise an error
macro_rules! starlark_fail_fn {
    ($fn: path, $t:expr) => (
        assert!($fn($t).is_err());
    );
    ($fn: path, $t:expr, $c:expr) => (
        assert_eq!($c, $fn($t).err().unwrap().code.unwrap());
    );
    ($fn: path, $t1:expr, $t2: expr, $c:expr) => (
        assert_eq!($c, $fn(&format!("{}{}", $t1, $t2))
                .err().unwrap().code.unwrap());
    );
}

/// A simple macro to execute a Starlark snippet and fails if the last statement is false.
macro_rules! starlark_ok {
    ($($t:expr),+) => (starlark_ok_fn!(testutil::starlark_empty, $($t),+))
}

/// Test that the execution of a starlark code raise an error
macro_rules! starlark_fail {
    ($($t:expr),+) => (starlark_fail_fn!(testutil::starlark_empty_no_diagnostic, $($t),+))
}
