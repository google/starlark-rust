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
use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use linked_hash_map::LinkedHashMap;
use std;
use std::cmp::Ordering;
use std::error::Error;
use std::num::NonZeroI64;
use std::sync;

use crate::environment::{Environment, TypeValues};
use crate::eval::noload::eval;
use crate::syntax::dialect::Dialect;
use crate::values::dict::Dictionary;
use crate::values::function::WrappedMethod;
use crate::values::none::NoneType;
use crate::values::range::Range;
use crate::values::*;

// Errors -- CR = Critical Runtime
const CHR_NOT_UTF8_CODEPOINT_ERROR_CODE: &str = "CR00";
const DICT_ITERABLE_NOT_PAIRS_ERROR_CODE: &str = "CR01";
const INT_CONVERSION_FAILED_ERROR_CODE: &str = "CR03";
const ORD_EXPECT_ONE_CHAR_ERROR_CODE: &str = "CR04";
const EMPTY_ITERABLE_ERROR_CODE: &str = "CR05";
const NUL_RANGE_STEP_ERROR_CODE: &str = "CR06";
const USER_FAILURE_ERROR_CODE: &str = "CR99";

#[macro_use]
pub mod macros;
pub mod dict;
mod freeze;
pub mod list;
pub mod string;
pub mod structs;

starlark_module! {global_functions =>
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
                st.print_with_newline_before(),
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
    any(x, /) {
        for i in &x.iter()? {
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
    all(x, /) {
        for i in &x.iter()? {
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
    bool(x = false, /) {
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
    chr(i, /) {
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
    /// # dict(one=1, two=2) == {'one': 1, 'two': 2}
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dict([(1, 2)], x=3) == {1: 2, 'x': 3}
    /// # )").unwrap());
    /// ```
    dict(?a, /, **kwargs) {
        let mut map = Dictionary::new();
        if let Some(a) = a {
            match a.get_type() {
                "dict" => {
                    for k in &a.iter()? {
                        let v = a.at(k.clone())?;
                        map.set_at(k, v)?;
                    }
                },
                _ => {
                   for el in &a.iter()? {
                       match el.iter() {
                           Ok(it) => {
                                let mut it = it.iter();
                                let first = it.next();
                                let second = it.next();
                                if first.is_none() || second.is_none() || it.next().is_some() {
                                    starlark_err!(
                                        DICT_ITERABLE_NOT_PAIRS_ERROR_CODE,
                                        format!(
                                            "Found a non-pair element in the positional argument of dict(): {}",
                                            el.to_repr(),
                                        ),
                                        "Non-pair element in first argument".to_owned()
                                    );
                                }
                                map.set_at(first.unwrap(), second.unwrap())?;
                           }
                           Err(..) =>
                               starlark_err!(
                                   DICT_ITERABLE_NOT_PAIRS_ERROR_CODE,
                                   format!(
                                       "Found a non-pair element in the positional argument of dict(): {}",
                                       el.to_repr(),
                                   ),
                                   "Non-pair element in first argument".to_owned()
                               ),
                       }
                   }
               }
           }
       }
       for (k, v) in kwargs {
           map.set_at(k.into(), v)?;
       }
       Ok(map)
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
    dir(env env, x, /) {
        let mut result = env.list_type_value(&x);
        if let Ok(v) = x.dir_attr() {
            result.extend(v);
        }
        result.sort();
        Ok(Value::from(result))
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
    /// # assert!(starlark_default(r#"(
    /// enumerate(["zero", "one", "two"]) == [(0, "zero"), (1, "one"), (2, "two")]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// enumerate(["one", "two"], 1) == [(1, "one"), (2, "two")]
    /// # )"#).unwrap());
    /// ```
    enumerate(it, offset: i64 = 0, /) {
        let v : Vec<Value> =
            it
            .iter()?
            .iter()
            .enumerate()
            .map(|(k, v)| Value::from((Value::new(k as i64 + offset), v)))
            .collect();
        Ok(Value::from(v))
    }

    /// [getattr](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#getattr
    /// ): returns the value of an attribute
    ///
    /// `getattr(x, name)` returns the value of the attribute (field or method) of x named `name`.
    /// It is a dynamic error if x has no such attribute.
    ///
    /// `getattr(x, "f")` is equivalent to `x.f`.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// getattr("banana", "split")("a") == ["b", "n", "n", ""] # equivalent to "banana".split("a")
    /// # "#).unwrap());
    /// ```
    getattr(env env, a, attr: String, default = NoneType::None, /) {
        match a.get_attr(&attr) {
            Ok(v) => Ok(v),
            x => match env.get_type_value(&a, &attr) {
                Some(v) => if v.get_type() == "function" {
                    // Insert self so the method see the object it is acting on
                    Ok(WrappedMethod::new(a.clone(), v))
                } else {
                    Ok(v)
                }
                None => if default.get_type() == "NoneType" { x } else { Ok(default) }
            }
        }
    }

    /// [hasattr](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#hasattr
    /// ): test if an object has an attribute
    ///
    /// `hasattr(x, name)` reports whether x has an attribute (field or method) named `name`.
    hasattr(env env, a, attr: String, /) {
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

    /// [hash](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#hash
    /// ): returns the hash number of a value.
    ///
    /// `hash(x)`` returns an integer hash value for x such that `x == y` implies
    /// `hash(x) == hash(y)``.
    ///
    /// `hash` fails if x, or any value upon which its hash depends, is unhashable.
    hash(a, /) {
        Ok(Value::new(a.get_hash()? as i64))
    }

    /// [int](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#int
    /// ): convert a value to integer.
    ///
    /// `int(x[, base])` interprets its argument as an integer.
    ///
    /// If x is an `int`, the result is x.
    /// If x is a `float`, the result is the integer value nearest to x,
    /// truncating towards zero; it is an error if x is not finite (`NaN`,
    /// `+Inf`, `-Inf`).
    /// If x is a `bool`, the result is 0 for `False` or 1 for `True`.
    ///
    /// If x is a string, it is interpreted like a string literal;
    /// an optional base prefix (`0`, `0b`, `0B`, `0x`, `0X`) determines which base to use.
    /// The string may specify an arbitrarily large integer,
    /// whereas true integer literals are restricted to 64 bits.
    /// If a non-zero `base` argument is provided, the string is interpreted
    /// in that base and no base prefix is permitted; the base argument may
    /// specified by name.
    ///
    /// `int()` with no arguments returns 0.
    int(a, /, ?base) {
        if a.get_type() == "string" {
            let s = a.to_str();
            let base = match base {
                Some(base) => base.to_int()?,
                None => 0,
            };
            if base == 1 || base < 0 || base > 36 {
                starlark_err!(
                    INT_CONVERSION_FAILED_ERROR_CODE,
                    format!(
                        "{} is not a valid base, int() base must be >= 2 and <= 36",
                        base,
                    ),
                    format!("Invalid base {}", base)
                )
            }
            let (sign, s) = {
                match s.chars().next() {
                    Some('+') => (1, s.get(1..).unwrap().to_string()),
                    Some('-') => (-1, s.get(1..).unwrap().to_string()),
                    _ => (1, s)
                }
            };
            let base = if base == 0 {
                match s.clone().get(0..2) {
                    Some("0b") | Some("0B") => 2,
                    Some("0o") | Some("0O") => 8,
                    Some("0x") | Some("0X") => 16,
                    _ => 10
                }
            } else { base as u32 };
            let s = match base {
                16 => if s.starts_with("0x") || s.starts_with("0X") {
                    s.get(2..).unwrap().to_string()
                } else { s },
                8 => if s.starts_with("0o") || s.starts_with("0O") {
                    s.get(2..).unwrap().to_string()
                } else {
                    s
                },
                2 => if s.starts_with("0b") || s.starts_with("0B") {
                    s.get(2..).unwrap().to_string()
                } else { s },
                _ => s
            };
            match i64::from_str_radix(&s, base) {
                Ok(i) => Ok(Value::new(sign * i)),
                Err(x) => starlark_err!(
                    INT_CONVERSION_FAILED_ERROR_CODE,
                    format!(
                        "{} is not a valid number in base {}: {}",
                        a.to_repr(),
                        base,
                        x.description(),
                    ),
                    format!("Not a base {} integer", base)
                ),
            }
        } else {
            match base {
                Some(base) => {
                    starlark_err!(
                        INT_CONVERSION_FAILED_ERROR_CODE,
                        "int() cannot convert non-string with explicit base".to_owned(),
                        format!("Explict base '{}' provided with non-string", base.to_repr())
                    )
                }
                None => Ok(Value::new(a.to_int()?)),
            }
        }
    }

    /// [len](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#len
    /// ): get the length of a sequence
    ///
    /// `len(x)` returns the number of elements in its argument.
    ///
    /// It is a dynamic error if its argument is not a sequence.
    len(a, /) {
        Ok(Value::new(a.length()?))
    }

    /// [list](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#list
    /// ): construct a list.
    ///
    /// `list(x)` returns a new list containing the elements of the
    /// iterable sequence x.
    ///
    /// With no argument, `list()` returns a new empty list.
    list(?a, /) {
        if let Some(a) = a {
            Ok(Value::from(a.to_vec()?))
        } else {
            Ok(Value::from(Vec::<Value>::new()))
        }
    }

    /// [max](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#max
    /// ): returns the maximum of a sequence.
    ///
    /// `max(x)` returns the greatest element in the iterable sequence x.
    ///
    /// It is an error if any element does not support ordered comparison,
    /// or if the sequence is empty.
    ///
    /// The optional named parameter `key` specifies a function to be applied
    /// to each element prior to comparison.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// max([3, 1, 4, 1, 5, 9])               == 9
    /// # and
    /// max("two", "three", "four")           == "two"    # the lexicographically greatest
    /// # and
    /// max("two", "three", "four", key=len)  == "three"  # the longest
    /// # )"#).unwrap());
    /// ```
    max(call_stack cs, env e, *args, ?key) {
        let args = if args.len() == 1 {
            args.swap_remove(0)
        } else {
            Value::from(args)
        };
        let it = args.iter()?;
        let mut it = it.iter();
        let mut max = match it.next() {
            Some(x) => x,
            None => starlark_err!(
                EMPTY_ITERABLE_ERROR_CODE,
                "Argument is an empty iterable, max() expect a non empty iterable".to_owned(),
                "Empty".to_owned()
            )
        };
        match key {
            None => {
                for i in it {
                    if max.compare(&i)? == Ordering::Less {
                        max = i;
                    }
                }
            }
            Some(key) => {
                let mut cached = key.call(cs, e.clone(), vec![max.clone()], LinkedHashMap::new(), None, None)?;
                for i in it {
                    let keyi = key.call(cs, e.clone(), vec![i.clone()], LinkedHashMap::new(), None, None)?;
                    if cached.compare(&keyi)? == Ordering::Less {
                        max = i;
                        cached = keyi;
                    }
                }
            }
        };
        Ok(max)
    }

    /// [min](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#min
    /// ): returns the minimum of a sequence.
    ///
    /// `min(x)` returns the least element in the iterable sequence x.
    ///
    /// It is an error if any element does not support ordered comparison,
    /// or if the sequence is empty.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// min([3, 1, 4, 1, 5, 9])                 == 1
    /// # and
    /// min("two", "three", "four")             == "four"  # the lexicographically least
    /// # and
    /// min("two", "three", "four", key=len)    == "two"   # the shortest
    /// # )"#).unwrap());
    /// ```
    min(call_stack cs, env e, *args, ?key) {
        let args = if args.len() == 1 {
            args.swap_remove(0)
        } else {
            Value::from(args)
        };
        let it = args.iter()?;
        let mut it = it.iter();
        let mut min = match it.next() {
            Some(x) => x,
            None => starlark_err!(
                EMPTY_ITERABLE_ERROR_CODE,
                "Argument is an empty iterable, min() expect a non empty iterable".to_owned(),
                "Empty".to_owned()
            )
        };
        match key {
            None => {
                for i in it {
                    if min.compare(&i)? == Ordering::Greater {
                        min = i;
                    }
                }
            }
            Some(key) => {
                let mut cached = key.call(cs, e.clone(), vec![min.clone()], LinkedHashMap::new(), None, None)?;
                for i in it {
                    let keyi = key.call(cs, e.clone(), vec![i.clone()], LinkedHashMap::new(), None, None)?;
                    if cached.compare(&keyi)? == Ordering::Greater {
                        min = i;
                        cached = keyi;
                    }
                }
            }
        };
        Ok(min)
    }

    /// [ord](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.mdord
    /// ): returns the codepoint of a character
    ///
    /// `ord(s)` returns the integer value of the sole Unicode code point encoded by the string `s`.
    ///
    /// If `s` does not encode exactly one Unicode code point, `ord` fails.
    /// Each invalid code within the string is treated as if it encodes the
    /// Unicode replacement character, U+FFFD.
    ///
    /// Example:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// ord("A")                                == 65
    /// # and
    /// ord("Й")                                == 1049
    /// # and
    /// ord("😿")                               == 0x1F63F
    /// # and
    /// ord("Й")                                == 1049
    /// # )"#).unwrap());
    /// ```
    ord(a, /) {
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
            Ok(Value::new(i64::from(u32::from(a.to_string().chars().next().unwrap()))))
        }
    }

    /// [range](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#range
    /// ): return a range of integers
    ///
    /// `range` returns a tuple of integers defined by the specified interval and stride.
    ///
    /// ```python
    /// range(stop)                             # equivalent to range(0, stop)
    /// range(start, stop)                      # equivalent to range(start, stop, 1)
    /// range(start, stop, step)
    /// ```
    ///
    /// `range` requires between one and three integer arguments.
    /// With one argument, `range(stop)` returns the ascending sequence of non-negative integers
    /// less than `stop`.
    /// With two arguments, `range(start, stop)` returns only integers not less than `start`.
    ///
    /// With three arguments, `range(start, stop, step)` returns integers
    /// formed by successively adding `step` to `start` until the value meets or passes `stop`.
    /// A call to `range` fails if the value of `step` is zero.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// list(range(10))                         == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    /// # and
    /// list(range(3, 10))                      == [3, 4, 5, 6, 7, 8, 9]
    /// # and
    /// list(range(3, 10, 2))                   == [3, 5, 7, 9]
    /// # and
    /// list(range(10, 3, -2))                  == [10, 8, 6, 4]
    /// # )"#).unwrap());
    /// ```
    range(a1: i64, ?a2: Option<i64>, ?a3: Option<i64>, /) {
        let start = match a2 {
            None => 0,
            Some(_) => a1,
        };
        let stop = match a2 {
            None => a1.to_int()?,
            Some(a2) => a2,
        };
        let step = match a3 {
            None => 1,
            Some(a3) => a3,
        };
        let step = match NonZeroI64::new(step) {
            Some(step) => step,
            None => {
                starlark_err!(
                    NUL_RANGE_STEP_ERROR_CODE,
                    "Third argument of range (step) cannot be null".to_owned(),
                    "Null range step".to_owned()
                )
            }
        };
        Ok(Value::new(Range::new(start, stop, step)))
    }

    /// [repr](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#repr
    /// ): formats its argument as a string.
    ///
    /// All strings in the result are double-quoted.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// repr(1)                 == '1'
    /// # and
    /// repr("x")               == "\"x\""
    /// # and
    /// repr([1, "x"])          == "[1, \"x\"]"
    /// # )"#).unwrap());
    /// ```
    repr(a, /) {
        Ok(Value::new(a.to_repr()))
    }

    /// [reversed](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#reversed
    /// ): reverse a sequence
    ///
    /// `reversed(x)` returns a new list containing the elements of the iterable sequence x in
    /// reverse order.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// reversed(range(5))                              == [4, 3, 2, 1, 0]
    /// # and
    /// reversed("stressed".split_codepoints())         == ["d", "e", "s", "s", "e", "r", "t", "s"]
    /// # and
    /// reversed({"one": 1, "two": 2}.keys())           == ["two", "one"]
    /// # )"#).unwrap());
    /// ```
    reversed(a, /) {
        let v: Vec<Value> = a.to_vec()?;
        let v: Vec<Value> = v.into_iter().rev().collect();
        Ok(Value::from(v))
    }

    /// [sorted](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#sorted
    /// ): sort a sequence
    ///
    /// `sorted(x)` returns a new list containing the elements of the iterable sequence x,
    /// in sorted order.  The sort algorithm is stable.
    ///
    /// The optional named parameter `reverse`, if true, causes `sorted` to
    /// return results in reverse sorted order.
    ///
    /// The optional named parameter `key` specifies a function of one
    /// argument to apply to obtain the value's sort key.
    /// The default behavior is the identity function.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// sorted([3, 1, 4, 1, 5, 9])                               == [1, 1, 3, 4, 5, 9]
    /// # and
    /// sorted([3, 1, 4, 1, 5, 9], reverse=True)                 == [9, 5, 4, 3, 1, 1]
    /// # and
    ///
    /// sorted(["two", "three", "four"], key=len)                == ["two", "four", "three"] # shortest to longest
    /// # and
    /// sorted(["two", "three", "four"], key=len, reverse=True)  == ["three", "four", "two"] # longest to shortest
    /// # )"#).unwrap());
    /// ```
    sorted(call_stack cs, env e, x, /, ?key, reverse = false) {
        let it = x.iter()?;
        let x = it.iter();
        let mut it = match key {
            None => {
                x.map(|x| (x.clone(), x)).collect()
            }
            Some(key) => {
                let mut v = Vec::new();
                for el in x {
                    v.push((
                        el.clone(),
                        key.call(cs, e.clone(), vec![el], LinkedHashMap::new(), None, None)?
                    ));
                }
                v
            }
        };

        let mut compare_ok = Ok(());

        let reverse = reverse.to_bool();
        it.sort_by(
            |x : &(Value, Value), y : &(Value, Value)| {
                let ord_or_err = if reverse {
                    x.1.compare(&y.1).map(Ordering::reverse)
                } else {
                    x.1.compare(&y.1)
                };
                match ord_or_err {
                    Ok(r) => r,
                    Err(e) => {
                        compare_ok = Err(e);
                        Ordering::Equal // does not matter
                    }
                }
            }
        );

        compare_ok?;

        let result : Vec<Value> = it.into_iter().map(|x| x.0).collect();
        Ok(Value::from(result))
    }

    /// [str](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#str
    /// ): formats its argument as a string.
    ///
    /// If x is a string, the result is x (without quotation).
    /// All other strings, such as elements of a list of strings, are double-quoted.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// str(1)                          == '1'
    /// # and
    /// str("x")                        == 'x'
    /// # and
    /// str([1, "x"])                   == "[1, \"x\"]"
    /// # )"#).unwrap());
    /// ```
    _str(a, /) {
        Ok(Value::new(a.to_str()))
    }

    /// [tuple](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#tuple
    /// ): returns a tuple containing the elements of the iterable x.
    ///
    /// With no arguments, `tuple()` returns the empty tuple.
    tuple(?a, /) {
        if let Some(a) = a {
            Ok(Value::new(tuple::Tuple::new(a.to_vec()?)))
        } else {
            Ok(Value::new(tuple::Tuple::new(Vec::new())))
        }
    }

    /// [type](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#type
    /// ): returns a string describing the type of its operand.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// type(None)              == "NoneType"
    /// # and
    /// type(0)                 == "int"
    /// # )"#).unwrap());
    /// ```
    _type(a, /) {
        Ok(Value::new(a.get_type().to_owned()))
    }

    /// [zip](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#zip
    /// ): zip several iterables together
    ///
    /// `zip()` returns a new list of n-tuples formed from corresponding
    /// elements of each of the n iterable sequences provided as arguments to
    /// `zip`.  That is, the first tuple contains the first element of each of
    /// the sequences, the second element contains the second element of each
    /// of the sequences, and so on.  The result list is only as long as the
    /// shortest of the input sequences.
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// zip()                                   == []
    /// # and
    /// zip(range(5))                           == [(0,), (1,), (2,), (3,), (4,)]
    /// # and
    /// zip(range(5), "abc".split_codepoints()) == [(0, "a"), (1, "b"), (2, "c")]
    /// # )"#).unwrap());
    /// ```
    zip(*args) {
        let mut v = Vec::new();

        for arg in args {
            let first = v.is_empty();
            let mut idx = 0;
            for e in &arg.iter()? {
                if first {
                    v.push(Value::from((e.clone(),)));
                    idx += 1;
                } else if idx < v.len() {
                    v[idx] = v[idx].add(Value::from((e.clone(),)))?;
                    idx += 1;
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
    env.set("None", Value::new(NoneType::None)).unwrap();
    env.set("True", Value::new(true)).unwrap();
    env.set("False", Value::new(false)).unwrap();
    dict::global(list::global(string::global(global_functions(env))))
}

/// Default global environment with added non-standard `struct` and `set` extensions.
pub fn global_environment_with_extensions() -> Environment {
    let env = global_environment();
    let env = structs::global(env);
    let env = freeze::global(env);
    crate::linked_hash_set::global(env)
}

/// Execute a starlark snippet with the default environment for test and return the truth value
/// of the last statement. Used for tests and documentation tests.
#[doc(hidden)]
pub fn starlark_default(snippet: &str) -> Result<bool, Diagnostic> {
    let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
    let env = global_environment_with_extensions();
    let mut test_env = env.freeze().child("test");
    match eval(
        &map,
        "<test>",
        snippet,
        Dialect::Bzl,
        &mut test_env,
        TypeValues::new(env),
    ) {
        Ok(v) => Ok(v.to_bool()),
        Err(d) => {
            Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[d.clone()]);
            Err(d)
        }
    }
}

#[cfg(test)]
pub mod tests {
    use super::global_environment;
    use super::starlark_default;
    use super::Dialect;
    use crate::environment::TypeValues;
    use crate::eval::noload::eval;
    use codemap::CodeMap;
    use codemap_diagnostic::Diagnostic;
    use std::sync;

    pub fn starlark_default_fail(snippet: &str) -> Result<bool, Diagnostic> {
        let map = sync::Arc::new(sync::Mutex::new(CodeMap::new()));
        let mut env = global_environment().freeze().child("test");
        match eval(
            &map,
            "<test>",
            snippet,
            Dialect::Bzl,
            &mut env,
            TypeValues::new(global_environment()),
        ) {
            Ok(v) => Ok(v.to_bool()),
            Err(d) => Err(d),
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
        starlark_ok!("(dict(one=1, two=2) == {'one': 1, 'two': 2})");
        starlark_ok!("(dict([(1, 2)], x=3) == {1: 2, 'x': 3})");
    }

    #[test]
    fn test_enumerate() {
        starlark_ok!(
            "(enumerate(['zero', 'one', 'two']) == [(0, 'zero'), (1, 'one'), (2, 'two')])"
        );
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
        starlark_ok!("(repr('x') == '\"x\"')");
        starlark_ok!("(repr([1, 'x']) == '[1, \"x\"]')");
    }

    #[test]
    fn test_str() {
        starlark_ok!("(str(1) == '1')");
        starlark_ok!("(str('x') == 'x')");
        starlark_ok!("(str([1, 'x']) == '[1, \"x\"]')");
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
        starlark_ok!("(zip(range(5), 'abc'.split_codepoints()) == [(0, 'a'), (1, 'b'), (2, 'c')])");
    }
}
