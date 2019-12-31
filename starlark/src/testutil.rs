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
use crate::environment;
use crate::environment::TypeValues;
use crate::eval;
use crate::eval::def::Def;
use crate::eval::noload;
use crate::stdlib::global_environment_for_repl_and_tests;
use crate::syntax::dialect::Dialect;
use crate::values::cell::ObjectRef;
use crate::values::Value;
use codemap::CodeMap;
use codemap_diagnostic::Diagnostic;
use std::sync;
use std::sync::Arc;
use std::sync::Mutex;

/// Execute a starlark snippet with the passed environment.
pub fn starlark_no_diagnostic(
    env: &mut environment::Environment,
    snippet: &str,
    type_values: &TypeValues,
) -> Result<bool, Diagnostic> {
    let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
    Ok(eval::noload::eval(&map, "<test>", snippet, Dialect::Bzl, env, type_values)?.to_bool())
}

/// A simple macro to execute a Starlark snippet and fails if the last statement is false.
macro_rules! starlark_ok_fn {
    ($fn:path, $t:expr) => {
        assert!($fn($t).unwrap());
    };
    ($fn:path, $t1:expr, $t2:expr) => {
        assert!($fn(&format!("{}{}", $t1, $t2)).unwrap());
    };
}

/// Test that the execution of a starlark code raise an error
macro_rules! starlark_fail_fn {
    ($fn:path, $t:expr) => {
        assert!($fn($t).is_err());
    };
    ($fn:path, $t:expr, $c:expr) => {
        assert_eq!($c, $fn($t).err().unwrap().code.unwrap());
    };
    ($fn:path, $t1:expr, $t2:expr, $c:expr) => {
        assert_eq!(
            $c,
            $fn(&format!("{}{}", $t1, $t2)).err().unwrap().code.unwrap()
        );
    };
}

/// A simple macro to execute a Starlark snippet and fails if the last statement is false.
macro_rules! starlark_ok {
    ($($t:expr),+) => (starlark_ok_fn!($crate::stdlib::starlark_default, $($t),+))
}

/// Test that the execution of a starlark code raise an error
macro_rules! starlark_fail {
    ($($t:expr),+) => (starlark_fail_fn!($crate::stdlib::tests::starlark_default_fail, $($t),+))
}

pub fn test_optimize_on_freeze(input: &str, expected: &str) {
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    let (global, type_values) = global_environment_for_repl_and_tests();
    global.freeze();
    let mut env = global.child("test");
    let f: Value = noload::eval(
        &map,
        "test",
        input,
        crate::syntax::dialect::Dialect::Bzl,
        &mut env,
        &type_values,
    )
    .unwrap();

    env.freeze();

    let def: ObjectRef<Def> = f.downcast_ref().unwrap();
    let mut actual = String::new();
    def.fmt_for_test(&mut actual, "").unwrap();
    assert_eq!(expected, &actual);
}
