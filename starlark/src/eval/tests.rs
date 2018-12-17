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

use eval::testutil;
use eval::RECURSION_ERROR_CODE;

#[test]
fn arithmetic_test() {
    starlark_ok!("(1 + 2 == 3)");
    starlark_ok!("(1 * 2 == 2)");
    starlark_ok!("(-1 * 2 == -2)");
    starlark_ok!("(5 / 2 == 2)");
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
    const F: &'static str = "
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
