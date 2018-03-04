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
use codemap_diagnostic::Diagnostic;
use values::TypedValue;
use eval;

/// Execute a starlark snippet with an empty environment.
pub fn starlark_exec(snippet: &str) -> Result<bool, Diagnostic> {
    let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
    let mut env = environment::Environment::new("test");
    Ok(eval::eval_str(&map, snippet, false, &mut env)?.to_bool())
}

/// A simple macro to execute a Starlark snippet and fails if the last statement is false.
macro_rules! starlark_ok {
    ($t:expr) => (
        assert!(testutil::starlark_exec($t).unwrap());
    );
    ($t1:expr, $t2:expr) => (
        assert!(testutil::starlark_exec(&format!("{}{}", $t1, $t2)).unwrap());
    );
}

/// Test that the execution of a starlark code raise an error
macro_rules! starlark_fail {
    ($t:expr) => (
        assert!(testutil::starlark_exec($t).is_err());
    );
    ($t:expr, $c:expr) => (
        assert_eq!($c, testutil::starlark_exec($t).err().unwrap().code.unwrap());
    );
    ($t1:expr, $t2: expr, $c:expr) => (
        assert_eq!($c, testutil::starlark_exec(&format!("{}{}", $t1, $t2))
                .err().unwrap().code.unwrap());
    );
}
