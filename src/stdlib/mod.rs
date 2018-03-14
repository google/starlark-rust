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

//! A module with the standard function and constants that are by default in all dialect of Starlark
use std::error::Error;
use std;
use std::collections::HashMap;
use std::sync;
use eval::simple::eval;
use codemap::CodeMap;
use codemap_diagnostic::{Diagnostic, Emitter, ColorConfig};

use values::*;
use linked_hash_map::LinkedHashMap;
use environment::Environment;

// Errors -- CR = Critical Runtime
const CHR_NOT_UTF8_CODEPOINT_ERROR_CODE: &'static str = "CR00";
const DICT_ITERABLE_NOT_PAIRS_ERROR_CODE: &'static str = "CR01";
const ATTR_NAME_NOT_STRING_ERROR_CODE: &'static str = "CR02";
const INT_CONVERSION_FAILED_ERROR_CODE: &'static str = "CR03";
const ORD_EXPECT_ONE_CHAR_ERROR_CODE: &'static str = "CR04";
const EMPTY_ITERABLE_ERROR_CODE: &'static str = "CR05";
const NUL_RANGE_STEP_ERROR_CODE: &'static str = "CR06";
const USER_FAILURE_ERROR_CODE: &'static str = "CR99";

#[macro_use]
pub mod macros;
pub mod string;
pub mod list;
pub mod dict;

starlark_module!{global_functions =>
    /// fail: fail the execution
    ///
    /// Examples:
    /// ```python
    /// fail("this is an error")  # Will fail with "this is an error"
    /// ```
    fail(call_stack st, msg) {
        starlark_err!(
            USER_FAILURE_ERROR_CODE,
            format!(
                "fail(): {}{}",
                msg.to_str(),
                st.into_iter().rev().fold(String::new(), |a,s| format!("{}\n    {}", a, s.1))
            ),
            msg.to_str()
        )
    }

    /// [any](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#any
    /// ): returns true if any value in the iterable object have a truth value of true.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// any([0, True]) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// any([0, 1]) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// any([0, 1, True]) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// any([0, 0]) == False
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// any([0, False]) == False
    /// # )").unwrap());
    /// ```
    any(#x) {
        for i in x.into_iter()? {
            if i.to_bool() {
                return Ok(Value::new(true));
            }
        }
        Ok(Value::new(false))
    }

    /// [all](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#all
    /// ): returns true if all values in the iterable object have a truth value of true.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// all([1, True]) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// all([1, 1]) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// all([0, 1, True]) == False
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// all([0, 0]) == False
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// all([0, False]) == False
    /// # )").unwrap());
    /// ```
    all(x) {
        for i in x.into_iter()? {
            if !i.to_bool() {
                return Ok(Value::new(false));
            }
        }
        Ok(Value::new(true))
    }

    /// [bool](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#bool
    /// ): returns the truth value of any starlark value.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// bool([]) == False
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// bool(True) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// bool(False) == False
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// bool(None) == False
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// bool(bool) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// bool(1) == True
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// bool(0) == False
    /// # )").unwrap());
    /// ```
    bool(#x) {
        Ok(Value::new(x.to_bool()))
    }

    /// [chr](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#bool
    /// ): returns a string encoding a codepoint.
    ///
    /// `chr(i)` returns a returns a string that encodes the single Unicode code point whose value is
    /// specified by the integer `i`. `chr` fails unless `0 ≤ i ≤ 0x10FFFF`.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// chr(65) == 'A'
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// chr(1049) == 'Й'
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// chr(0x1F63F) == '😿'
    /// # )").unwrap());
    /// ```
    chr(i) {
        let cp = i.to_int()? as u32;
        match std::char::from_u32(cp) {
            Some(x) => Ok(Value::new(x.to_string())),
            None => starlark_err!(CHR_NOT_UTF8_CODEPOINT_ERROR_CODE,
                format!(
                    "chr() parameter value is 0x{:x} which is not a valid UTF-8 codepoint",
                    cp
                ),
                "Parameter to chr() is not a valid UTF-8 codepoint".to_owned()
            ),
        }
    }


    /// [dict](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#dict
    /// ): creates a dictionary.
    ///
    /// `dict` creates a dictionary. It accepts up to one positional argument, which is interpreted
    /// as an iterable of two-element sequences (pairs), each specifying a key/value pair in the
    /// resulting dictionary.
    ///
    /// `dict` also accepts any number of keyword arguments, each of which specifies a key/value
    /// pair in the resulting dictionary; each keyword is treated as a string.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// dict() == {}
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dict([(1, 2), (3, 4)]) == {1: 2, 3: 4}
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dict([(1, 2), ['a', 'b']]) == {1: 2, 'a': 'b'}
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// # dict(one=1, two=2) == {'one': 1, 'two': 1}
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dict([(1, 2)], x=3) == {1: 2, 'x': 3}
    /// # )").unwrap());
    /// ```
    dict(#a = None, **kwargs) {
        let mut map = LinkedHashMap::new();
        if a.get_type() != "NoneType" {
           for el in a.into_iter()? {
               if el.length()? != 2 {
                   starlark_err!(
                       DICT_ITERABLE_NOT_PAIRS_ERROR_CODE,
                       format!(
                           "Found a non-pair element in the positional argument of dict(): {}",
                           el.to_repr(),
                       ),
                       "Non-pair element in first argument".to_owned()
                   );
               } else {
                   map.insert(el.at(Value::new(0))?, el.at(Value::new(1))?);
               }
           }
       }
       for el in kwargs.into_iter()? {
           map.insert(el.clone(), kwargs.at(el)?);
       }
       Ok(Value::from(map))
    }

    /// [dir](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#dir
    /// ): list attributes of a value.
    ///
    /// `dir(x)` returns a list of the names of the attributes (fields and methods) of its operand.
    /// The attributes of a value `x` are the names `f` such that `x.f` is a valid expression.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(stringify!((
    /// "capitalize" in dir("abc")
    /// # ))).unwrap());
    /// ```
    dir(env env, x) {
        match x.dir_attr() {
            Ok(v) => Ok(Value::from(env.list_type_value(&x).extend(v))),
            _ => Ok(Value::from(env.list_type_value(&x))),
        }
    }


    /// [enumerate](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#enumerate
    /// ): return a list of (index, element) from an iterable.
    ///
    /// `enumerate(x)` returns a list of `(index, value)` pairs, each containing successive values of
    /// the iterable sequence and the index of the value within the sequence.
    ///
    /// The optional second parameter, `start`, specifies an integer value to add to each index.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// # enumerate(['zero', 'one', 'two']) == [(0, 'zero'), (1, 'one'), (2, 'two')]
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// # enumerate(['one', 'two'], 1) == [(1, 'one'), (2, 'two')]
    /// # )").unwrap());
    /// ```
    enumerate(#it, #offset = 0) {
        let v2 = offset.to_int()?;
        let v : Vec<Value> =
            it
            .into_iter()?
            .enumerate()
            .map(|(k, v)| Value::from((Value::new(k as i64 + v2), v)))
            .collect();
        for x in v.iter() {
            println!("Got {}", x.to_repr());
        }
        Ok(Value::from(v))
    }


    getattr(env env, #a, #attr) {
        if attr.get_type() != "string" {
            starlark_err!(
                ATTR_NAME_NOT_STRING_ERROR_CODE,
                format!(
                    "Second arg of getattr() is of type {} while expecting type string",
                    attr.get_type(),
                ),
                "Non string argument".to_owned()
            );
        } else {
            let attr = attr.to_str();
            match a.get_attr(&attr) {
                Ok(v) => Ok(v),
                x => match env.get_type_value(&a, &attr) {
                    Some(v) => Ok(v),
                    None => x
                }
            }
        }
    }

    hasattr(env env, #a, #attr) {
        if attr.get_type() != "string" {
            starlark_err!(
                ATTR_NAME_NOT_STRING_ERROR_CODE,
                format!(
                    "Second arg of hasattr() is of type {} while expecting type string",
                    attr.get_type(),
                ),
                "Non string argument".to_owned()
            )
        } else {
            let attr = attr.to_str();
            Ok(Value::new(
                match env.get_type_value(&a, &attr) {
                    Some(..) => true,
                    None => match a.has_attr(&attr) {
                        Ok(v) => v,
                        _ => false,
                    }
                }
            ))
        }
    }

    hash(#a) {
        Ok(Value::new(a.get_hash()? as i64))
    }

    int(#a, #radix = 10) {
        if a.get_type() == "string" {
            let s = a.to_str();
            let radix = radix.to_int()? as u32;
            match i64::from_str_radix(&s, radix) {
                Ok(i) => Ok(Value::new(i)),
                Err(x) => starlark_err!(
                    INT_CONVERSION_FAILED_ERROR_CODE,
                    format!(
                        "{} is not a valid number in base {}: {}",
                        a.to_repr(),
                        radix,
                        x.description(),
                    ),
                    format!("Not a base {} integer", radix)
                ),
            }
        } else {
            Ok(Value::new(a.to_int()?))
        }
    }

    len(#a) {
        Ok(Value::new(a.length()?))
    }

    list(#a = None) {
        let mut l = Vec::new();
        if a.get_type() != "NoneType" {
            for x in a.into_iter()? {
                l.push(x.clone())
            }
        }
        Ok(Value::from(l))
    }

    max(call_stack cs, env e, *args, key=None) {
        let args = if args.length()? == 1 {
            args.at(Value::new(0))?
        } else {
            args
        };
        let mut it = args.into_iter()?;
        let mut max = match it.next() {
            Some(x) => x,
            None => starlark_err!(
                EMPTY_ITERABLE_ERROR_CODE,
                "Argument is an empty iterable, max() expect a non empty iterable".to_owned(),
                "Empty".to_owned()
            )
        };
        if key.get_type() == "NoneType" {
            for i in it {
                if max < i {
                    max = i;
                }
            }
        } else {
            let mut cached = key.call(cs, e.child("max"), vec![max.clone()], HashMap::new(), None, None)?;
            for i in it {
                let keyi = key.call(cs, e.child("max"), vec![i.clone()], HashMap::new(), None, None)?;
                if cached < keyi {
                    max = i;
                    cached = keyi;
                }
            }
        }
        Ok(max)
    }

    min(call_stack cs, env e, *args, key=None) {
        let args = if args.length()? == 1 {
            args.at(Value::new(0))?
        } else {
            args
        };
        let mut it = args.into_iter()?;
        let mut min = match it.next() {
            Some(x) => x,
            None => starlark_err!(
                EMPTY_ITERABLE_ERROR_CODE,
                "Argument is an empty iterable, min() expect a non empty iterable".to_owned(),
                "Empty".to_owned()
            )
        };
        if key.get_type() == "NoneType" {
            for i in it {
                if min > i {
                    min = i;
                }
            }
        } else {
            let mut cached = key.call(cs, e.child("min"), vec![min.clone()], HashMap::new(), None, None)?;
            for i in it {
                let keyi = key.call(cs, e.child("min"), vec![i.clone()], HashMap::new(), None, None)?;
                if cached > keyi {
                    min = i;
                    cached = keyi;
                }
            }
        }
        Ok(min)
    }

    ord(#a) {
        if a.get_type() != "string" || a.length()? != 1 {
            starlark_err!(
                ORD_EXPECT_ONE_CHAR_ERROR_CODE,
                format!(
                    "ord(): {} is not a one character string",
                    a.to_repr(),
                ),
                "Not a one character string".to_owned()
            )
        } else {
            Ok(Value::new(u32::from(a.to_string().chars().next().unwrap()) as i64))
        }
    }

    range(#a1, #a2 = None, #a3 = None) {
        let start = if a2.get_type() == "NoneType" { 0 } else { a1.to_int()? };
        let stop = if a2.get_type() == "NoneType" { a1.to_int()? } else { a2.to_int()? };
        let step = if a3.get_type() == "NoneType" { 1 } else { a3.to_int()? };
        let mut r = Vec::new();
        let mut idx : i64 = start;
        if step == 0 {
            starlark_err!(
                NUL_RANGE_STEP_ERROR_CODE,
                "Third argument of range (step) cannot be null".to_owned(),
                "Null range step".to_owned()
            )
        }
        if step > 0 {
            while idx < stop {
                r.push(Value::new(idx));
                idx += step;
            }
        } else {
            while idx > stop {
                r.push(Value::new(idx));
                idx += step;
            }
        }
        Ok(tuple::Tuple::new(r.as_slice()))
    }

    repr(#a) {
        Ok(Value::new(a.to_repr()))
    }

    reversed(#a) {
        let v : Vec<Value> = a.into_iter()?.collect();
        let v : Vec<Value> = v.into_iter().rev().collect();
        Ok(Value::from(v))
    }

    sorted(call_stack cs, env e, #x, key = None, reverse = false) {
        let x = x.into_iter()?;
        let mut it : Vec<(Value, Value)> = if key.get_type() == "NoneType" {
            x.map(|x| (x.clone(), x)).collect()
        } else {
            let mut v = Vec::new();
            for el in x {
                v.push((
                    el.clone(),
                    key.call(cs, e.child("sorted"), vec![el], HashMap::new(), None, None)?
                ));
            }
            v
        };
        let reverse = reverse.to_bool();
        it.sort_by(
            |x : &(Value, Value), y : &(Value, Value)| {
                if reverse {
                    x.1.compare(y.1.clone()).reverse()
                } else {
                    x.1.compare(y.1.clone())
                }
            }
        );
        let result : Vec<Value> = it.into_iter().map(|x| x.0).collect();
        Ok(Value::from(result))
    }

    _str(#a) {
        Ok(Value::new(a.to_str()))
    }

    tuple(#a = None) {
        let mut l = Vec::new();
        if a.get_type() != "NoneType" {
            for x in a.into_iter()? {
                l.push(x.clone())
            }
        }
        Ok(Value::new(tuple::Tuple::new(l.as_slice())))
    }

    _type(#a) {
        Ok(Value::new(a.get_type().to_owned()))
    }

    zip(*args) {
        let mut v = Vec::new();

        for arg in args.into_iter()? {
            let first = v.is_empty();
            let mut idx = 0;
            for e in arg.into_iter()? {
                if first {
                    v.push(Value::from((e.clone(),)));
                    idx += 1;
                } else {
                    if idx < v.len() {
                        v[idx] = v[idx].add(Value::from((e.clone(),)))?;
                        idx += 1;
                    }
                }
            }
            v.truncate(idx);
        }
        Ok(Value::from(v))
    }
}

/// Return the default global environment, it is not yet frozen so that a caller can refine it.
///
/// For example `stdlib::global_environment().freeze().child("test")` create a child environment
/// of this global environment that have been frozen.
pub fn global_environment() -> Environment {
    let env = Environment::new("global");
    env.set("None", Value::new(None)).unwrap();
    env.set("True", Value::new(true)).unwrap();
    env.set("False", Value::new(false)).unwrap();
    dict::global(list::global(string::global(global_functions(env))))
}

/// Execute a starlark snippet with the default environment for test and return the truth value
/// of the last statement. Used for tests and documentation tests.
#[doc(hidden)]
pub fn starlark_default(snippet: &str) -> Result<bool, Diagnostic> {
    let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
    let mut env = global_environment().freeze().child("test");
    match eval(&map, "<test>", snippet, false, &mut env) {
        Ok(v) => Ok(v.to_bool()),
        Err(d) => {
            Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[d.clone()]);
            Err(d)
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::starlark_default;
    use std::sync;
    use codemap::CodeMap;
    use codemap_diagnostic::Diagnostic;
    use super::global_environment;
    use eval::simple::eval;
    use values::TypedValue;

    pub fn starlark_default_fail(snippet: &str) -> Result<bool, Diagnostic> {
        let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
        let mut env = global_environment().freeze().child("test");
        match eval(&map, "<test>", snippet, false, &mut env) {
            Ok(v) => Ok(v.to_bool()),
            Err(d) => Err(d)
        }
    }

    /// A simple macro to execute a Starlark snippet and fails if the last statement is false.
    macro_rules! starlark_ok {
        ($($t:expr),+) => (starlark_ok_fn!(starlark_default, $($t),+))
    }

    /// Test that the execution of a starlark code raise an error
    macro_rules! starlark_fail {
        ($($t:expr),+) => (starlark_fail_fn!(starlark_default_fail, $($t),+))
    }

    #[test]
    fn test_const() {
        starlark_ok!("(not None)");
        starlark_ok!("(not False)");
        starlark_ok!("True");
    }

    #[test]
    fn test_any() {
        starlark_ok!("any([0, True])");
        starlark_ok!("any([0, 1])");
        starlark_ok!("any([0, 1, True])");
        starlark_ok!("(not any([0, 0]))");
        starlark_ok!("(not any([0, False]))");
    }

    #[test]
    fn test_all() {
        starlark_ok!("all([True, True])");
        starlark_ok!("all([True, 1])");
        starlark_ok!("all([True, 1, True])");
        starlark_ok!("(not all([True, 0]))");
        starlark_ok!("(not all([1, False]))");
    }

    #[test]
    fn test_bool() {
        // bool
        starlark_ok!("bool(True)");
        starlark_ok!("(not bool(False))");
        // NoneType
        starlark_ok!("(not bool(None))");
        // int
        starlark_ok!("bool(1)");
        starlark_ok!("(not bool(0))");
        // dict
        starlark_ok!("(not bool({}))");
        starlark_ok!("bool({1:2})");
        // tuple
        starlark_ok!("(not bool(()))");
        starlark_ok!("bool((1,))");
        // list
        starlark_ok!("(not bool([]))");
        starlark_ok!("bool([1])");
        // string
        starlark_ok!("(not bool(''))");
        starlark_ok!("bool('1')");
        // function
        starlark_ok!("bool(bool)");
    }

    #[test]
    fn test_chr() {
        starlark_ok!("(chr(65) == 'A')");
        starlark_ok!("(chr(1049) == 'Й')");
        starlark_ok!("(chr(0x1F63F) == '😿')");
        starlark_fail!("chr(0x110000)", super::CHR_NOT_UTF8_CODEPOINT_ERROR_CODE);
    }

    #[test]
    fn test_ord() {
        starlark_ok!("(65 == ord('A'))");
        starlark_ok!("(1049 == ord('Й'))");
        starlark_ok!("(0x1F63F == ord('😿'))");
    }

    #[test]
    fn test_dict() {
        starlark_ok!("(dict() == {})");
        starlark_ok!("(dict([(1, 2), (3, 4)]) == {1: 2, 3: 4})");
        starlark_ok!("(dict([(1, 2), ['a', 'b']]) == {1: 2, 'a': 'b'})");
        starlark_ok!("(dict(one=1, two=2) == {'one': 1, 'two': 1})");
        starlark_ok!("(dict([(1, 2)], x=3) == {1: 2, 'x': 3})");
    }

    #[test]
    fn test_enumerate() {
        starlark_ok!("(enumerate(['zero', 'one', 'two']) == [(0, 'zero'), (1, 'one'), (2, 'two')])");
        starlark_ok!("(enumerate(['one', 'two'], 1) == [(1, 'one'), (2, 'two')])");
    }

    #[test]
    fn test_hash() {
        starlark_ok!("(hash(1) == 1)");
        starlark_ok!("(hash(2) == 2)");
    }

    #[test]
    fn test_int() {
        starlark_ok!("(int(1) == 1)");
        starlark_ok!("(int(False) == 0)");
        starlark_ok!("(int(True) == 1)");
        starlark_ok!("(int('1') == 1)");
        starlark_ok!("(int('16') == 16)");
        starlark_ok!("(int('16', 10) == 16)");
        starlark_ok!("(int('16', 8) == 14)");
        starlark_ok!("(int('16', 16) == 22)");
    }

    #[test]
    fn test_len() {
        starlark_ok!("(len(()) == 0)");
        starlark_ok!("(len({}) == 0)");
        starlark_ok!("(len([]) == 0)");
        starlark_ok!("(len([1]) == 1)");
        starlark_ok!("(len([1,2]) == 2)");
        starlark_ok!("(len({'16': 10}) == 1)");
    }

    #[test]
    fn test_list() {
        starlark_ok!("(list() == [])");
        starlark_ok!("(list((1,2,3)) == [1, 2, 3])");
    }

    #[test]
    fn test_repr() {
        starlark_ok!("(repr(1) == '1')");
        starlark_ok!("(repr('x') == \"'x'\")");
        starlark_ok!("(repr([1, 'x']) == \"[1, 'x']\")");
    }

    #[test]
    fn test_str() {
        starlark_ok!("(str(1) == '1')");
        starlark_ok!("(str('x') == 'x')");
        starlark_ok!("(str([1, 'x']) == \"[1, 'x']\")");
    }

    #[test]
    fn test_tuple() {
        starlark_ok!("(tuple() == ())");
        starlark_ok!("(tuple([1,2,3]) == (1, 2, 3))");
    }

    #[test]
    fn test_type() {
        starlark_ok!("(type(()) == 'tuple')");
        starlark_ok!("(type(1) == 'int')");
        starlark_ok!("(type('string') == 'string')");
        starlark_ok!("(type(None) == 'NoneType')");
    }

    #[test]
    fn test_min() {
        starlark_ok!("(min([3, 1, 4, 1, 5, 9]) == 1)");
        starlark_ok!("(min('two', 'three', 'four') == 'four')");
        starlark_ok!("(min('two', 'three', 'four', key=len) == 'two')");
    }

    #[test]
    fn test_max() {
        starlark_ok!("(max([3, 1, 4, 1, 5, 9]) == 9)");
        starlark_ok!("(max('two', 'three', 'four') == 'two')");
        starlark_ok!("(max('two', 'three', 'four', key=len) == 'three')");
    }

    #[test]
    fn test_reversed() {
        starlark_ok!("(reversed(['a', 'b', 'c']) == ['c', 'b', 'a'])");
        starlark_ok!("(reversed(range(5)) == [4, 3, 2, 1, 0])");
        starlark_ok!("(reversed({'one': 1, 'two': 2}.keys()) == ['two', 'one'])");
    }

    #[test]
    fn test_range() {
        starlark_ok!("(list(range(10)) == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])");
        starlark_ok!("(list(range(3, 10)) == [3, 4, 5, 6, 7, 8, 9])");
        starlark_ok!("(list(range(3, 10, 2)) == [3, 5, 7, 9])");
        starlark_ok!("(list(range(10, 3, -2)) == [10, 8, 6, 4])");
    }

    #[test]
    fn test_sorted() {
        starlark_ok!("(sorted([3, 1, 4, 1, 5, 9]) == [1, 1, 3, 4, 5, 9])");
        starlark_ok!("(sorted([3, 1, 4, 1, 5, 9], reverse=True) == [9, 5, 4, 3, 1, 1])");

        starlark_ok!("(sorted(['two', 'three', 'four'], key=len) == ['two', 'four', 'three'])");
        starlark_ok!(
            "(sorted(['two', 'three', 'four'], key=len, reverse=True) == ['three', 'four', 'two'])"
        );
    }

    #[test]
    fn test_zip() {
        starlark_ok!("(zip() == [])");
        starlark_ok!("(zip(range(5)) == [(0,), (1,), (2,), (3,), (4,)])");
        starlark_ok!("(zip(range(5), 'abc') == [(0, 'a'), (1, 'b'), (2, 'c')])");
    }
}
