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

use crate::environment::Environment;
use crate::environment::TypeValues;
use crate::eval::eval;
use crate::eval::testutil::starlark_no_diagnostic;
use crate::eval::EvalException;
use crate::eval::FileLoader;
use crate::eval::{noload, RECURSION_ERROR_CODE};
use crate::syntax::dialect::Dialect;
use crate::values::Value;
use codemap::CodeMap;
use std::sync::{Arc, Mutex};

#[test]
fn arithmetic_test() {
    starlark_ok!("(1 + 2 == 3)");
    starlark_ok!("(1 * 2 == 2)");
    starlark_ok!("(-1 * 2 == -2)");
    starlark_ok!("(5 // 2 == 2)");
    starlark_ok!("(5 % 2 == 1)");
}

#[test]
fn alias_test() {
    starlark_ok!(
        r#"
a = [1, 2, 3]
b = a
a[2] = 0
a == [1, 2, 0] and b == [1, 2, 0]
"#
    )
}

#[test]
fn recursive_list() {
    starlark_fail!(
        r#"
cyclic = [1, 2, 3]
cyclic[1] = cyclic
"#
    )
}

#[test]
fn funcall_test() {
    const F: &str = "
def f1():
  return 1

def f2(a): return a

def f3(a, b, c):
   return a + b + c

def f4(a, *args):
    r = a
    for i in args:
      r += i
    return r

def f5(a, **kwargs): return kwargs

def rec1(): rec1()

def rec2(): rec3()
def rec3(): rec4()
def rec4(): rec5()
def rec5(): rec6()
def rec6(): rec2()
";
    starlark_ok!(F, "(f1() == 1)");
    starlark_ok!(F, "(f2(2) == 2)");
    starlark_ok!(F, "(f3(1, 2, 3) == 6)");
    starlark_ok!(F, "(f4(1, 2, 3) == 6)");
    starlark_ok!(F, "(f5(2) == {})");
    starlark_ok!(F, "(f5(a=2) == {})");
    starlark_ok!(F, "(f5(1, b=2) == {'b': 2})");
    starlark_fail!(F, "rec1()", RECURSION_ERROR_CODE);
    starlark_fail!(F, "rec2()", RECURSION_ERROR_CODE);
    // multiple argument with the same name should not be allowed
    starlark_fail!("def f(a, a=2): pass");
    // Invalid order of parameter
    starlark_fail!("def f(a, *args, b): pass");
    starlark_fail!("def f(a, *args, b=1): pass");
    starlark_fail!("def f(a, b=1, *args, c=1): pass");
    starlark_fail!("def f(a, **kwargs, b=1): pass");
    starlark_fail!("def f(a, b=1, **kwargs, c=1): pass");
    starlark_fail!("def f(a, **kwargs, *args): pass");
}

#[test]
fn sets_disabled() {
    let (mut env, type_values) = crate::stdlib::global_environment();
    let err = starlark_no_diagnostic(&mut env, "s = {1, 2, 3}", &type_values).unwrap_err();
    assert_eq!(
        err.message,
        "Type `set` is not supported. Perhaps you need to enable some crate feature?".to_string()
    );
    assert_eq!(err.level, codemap_diagnostic::Level::Error);
    assert_eq!(
        err.code,
        Some(crate::values::error::NOT_SUPPORTED_ERROR_CODE.to_string())
    );
}

#[test]
fn sets() {
    fn env_with_set() -> (Environment, TypeValues) {
        let (mut env, mut type_values) = crate::stdlib::global_environment();
        crate::linked_hash_set::global(&mut env, &mut type_values);
        (env, type_values)
    }

    fn starlark_ok_with_global_env(snippet: &str) {
        let (mut env, type_values) = env_with_set();
        assert!(starlark_no_diagnostic(&mut env, snippet, &type_values,).unwrap());
    }

    starlark_ok_with_global_env(
        "s1 = {1, 2, 3, 1} ; s2 = set([1, 2, 3]) ; len(s1) == 3 and s1 == s2",
    );
    starlark_ok_with_global_env("list(set([1, 2, 3, 1])) == [1, 2, 3]");
    starlark_ok_with_global_env("list(set()) == []");
    starlark_ok_with_global_env("not set()");

    let (parent_env, type_values) = env_with_set();
    assert!(starlark_no_diagnostic(
        &mut parent_env.child("child"),
        "len({1, 2}) == 2",
        &type_values,
    )
    .unwrap());
}

#[test]
fn test_context_captured() {
    #[derive(Clone)]
    struct TestContextCapturedFileLoader {}

    impl FileLoader for TestContextCapturedFileLoader {
        fn load(&self, path: &str, type_values: &TypeValues) -> Result<Environment, EvalException> {
            assert_eq!("f.bzl", path);
            let mut env = Environment::new("new");
            // Check that `x` is captured with the function
            let f_bzl = r#"
x = 17
def f(): return x
"#;
            noload::eval(
                &Arc::new(Mutex::new(CodeMap::new())),
                path,
                f_bzl,
                Dialect::Bzl,
                &mut env,
                type_values,
            )
            .unwrap();
            env.freeze();
            Ok(env)
        }
    }

    let mut env = Environment::new("z");
    // Import `f` but do not import `x`
    let program = "load('f.bzl', 'f')\nf()";
    assert_eq!(
        Value::new(17),
        eval(
            &Arc::new(Mutex::new(CodeMap::new())),
            "outer.build",
            program,
            Dialect::Build,
            &mut env,
            &TypeValues::default(),
            &TestContextCapturedFileLoader {}
        )
        .unwrap()
    );
}

#[test]
fn test_type_values_are_imported_from_caller() {
    use crate::starlark_fun;
    use crate::starlark_module;
    use crate::starlark_parse_param_type;
    use crate::starlark_signature;
    use crate::starlark_signature_extraction;
    use crate::starlark_signatures;

    starlark_module! { string_truncate =>
        string.truncate(this: String, len: usize) {
            // This works properly only for ASCII, but that enough for a test
            this.truncate(len);
            Ok(Value::new(this))
        }
    }

    struct MyFileLoader {}

    impl FileLoader for MyFileLoader {
        fn load(&self, path: &str, type_values: &TypeValues) -> Result<Environment, EvalException> {
            assert_eq!("utils.bzl", path);

            let mut env = Environment::new("utils.bzl");
            noload::eval(
                &Arc::new(Mutex::new(CodeMap::new())),
                "utils.bzl",
                "def truncate_strings(strings, len): return [s.truncate(len) for s in strings]",
                Dialect::Bzl,
                &mut env,
                type_values,
            )?;
            Ok(env)
        }
    }

    let mut env = Environment::new("my.bzl");

    let mut type_values = TypeValues::default();
    string_truncate(&mut Environment::new("ignore"), &mut type_values);

    // Note `string.truncate` is not available in either `utils.bzl` or `my.bzl`,
    // but this code works.
    let result = eval(
        &Arc::new(Mutex::new(CodeMap::new())),
        "my.bzl",
        "load('utils.bzl', 'truncate_strings'); truncate_strings(['abc', 'de'], 2)",
        Dialect::Bzl,
        &mut env,
        &type_values,
        &MyFileLoader {},
    )
    .unwrap();

    assert_eq!("[\"ab\", \"de\"]", result.to_str());
}
