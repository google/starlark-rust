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

//! Define the string type for Starlark.
use std;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use values::*;

impl TypedValue for String {
    immutable!();
    any!();

    fn to_str(&self) -> String {
        self.clone()
    }
    fn to_repr(&self) -> String {
        format!(
            "'{}'",
            self.chars()
                .map(|x| -> String { x.escape_debug().collect() })
                .fold("".to_string(), |accum, s| accum + &s)
        )
    }

    not_supported!(to_int);
    fn get_type(&self) -> &'static str {
        "string"
    }
    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        let mut s = DefaultHasher::new();
        self.hash(&mut s);
        Ok(s.finish())
    }

    fn compare(&self, other: &Value, _recursion: u32) -> Result<Ordering, ValueError> {
        if other.get_type() == "string" {
            Ok(self.cmp(&other.to_str()))
        } else {
            default_compare(self, other)
        }
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.len() as i64)? as usize;
        Ok(Value::new(self.chars().skip(i).next().unwrap().to_string()))
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.chars().count() as i64)
    }

    fn is_in(&self, other: &Value) -> ValueResult {
        if other.get_type() == "string" {
            Ok(Value::new(self.contains(&other.to_str())))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    fn is_descendant(&self, _other: &TypedValue) -> bool {
        false
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        let (start, stop, stride) =
            Value::convert_slice_indices(self.len() as i64, start, stop, stride)?;
        let (low, take, astride) = if stride < 0 {
            (stop + 1, start - stop, -stride)
        } else {
            (start, stop - start, stride)
        };
        if take <= 0 {
            return Ok(Value::from(""));
        };

        let v: String = self
            .chars()
            .skip(low as usize)
            .take(take as usize)
            .collect();
        let v: String = if stride > 0 {
            v.chars()
                .enumerate()
                .filter_map(|x| {
                    if 0 == (x.0 as i64 % astride) {
                        Some(x.1)
                    } else {
                        None
                    }
                })
                .collect()
        } else {
            v.chars()
                .rev()
                .enumerate()
                .filter_map(|x| {
                    if 0 == (x.0 as i64 % astride) {
                        Some(x.1)
                    } else {
                        None
                    }
                })
                .collect()
        };
        Ok(Value::new(v))
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a string.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// // "abc" + "def" = "abcdef"
    /// Value::from("abc").add(Value::from("def")).unwrap() == Value::from("abcdef")
    /// # );
    /// ```
    fn add(&self, other: Value) -> ValueResult {
        if other.get_type() == "string" {
            let s: String = self.chars().chain(other.to_str().chars()).collect();
            Ok(Value::new(s))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    /// Repeat `other` times this string.
    ///
    /// `other` has to be an int.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// // "abc" * 3 == "abcabcabc"
    /// Value::from("abc").mul(Value::from(3)).unwrap() == Value::from("abcabcabc")
    /// # );
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        if other.get_type() == "int" {
            let l = other.to_int()?;
            let mut result = String::new();
            for _i in 0..l {
                result += self
            }
            Ok(Value::new(result))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    /// Perform string interpolation
    ///
    /// Cf. [String interpolation on the Starlark spec](
    /// https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#string-interpolation
    /// )
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # use std::collections::HashMap;
    /// # assert!(
    /// // "Hello %s, your score is %d" % ("Bob", 75) == "Hello Bob, your score is 75"
    /// Value::from("Hello %s, your score is %d").percent(Value::from(("Bob", 75))).unwrap()
    ///     == Value::from("Hello Bob, your score is 75")
    /// # );
    /// # assert!(
    /// // "%d %o %x %c" % (65, 65, 65, 65) == "65 101 41 A"
    /// Value::from("%d %o %x %c").percent(Value::from((65, 65, 65, 65))).unwrap()
    ///     == Value::from("65 101 41 A")
    /// # );
    /// // "%(greeting)s, %(audience)s" % {"greeting": "Hello", "audience": "world"} ==
    /// //      "Hello, world"
    /// let mut d = Value::from(HashMap::<Value, Value>::new());
    /// d.set_at(Value::from("greeting"), Value::from("Hello"));
    /// d.set_at(Value::from("audience"), Value::from("world"));
    /// # assert!(
    /// Value::from("%(greeting)s, %(audience)s").percent(d).unwrap() == Value::from("Hello, world")
    /// # );
    /// ```
    fn percent(&self, other: Value) -> ValueResult {
        let mut split_it = self.split("%");
        let mut res = String::new();
        let mut idx = 0;
        let mut len = 0;
        res += split_it.next().unwrap_or("");
        let mut last_percent = false;
        for s in split_it {
            if s.is_empty() {
                last_percent = !last_percent;
                res.push('%');
            } else if !last_percent {
                let mut chars = s.chars().peekable();
                let var = if let Some(&'(') = chars.peek() {
                    let mut varname = String::new();
                    chars.next();
                    loop {
                        match chars.next() {
                            Some(')') => break,
                            Some(ref x) => varname.push(*x),
                            None => return Err(ValueError::InterpolationFormat),
                        }
                    }
                    other.at(Value::new(varname))?.clone()
                } else {
                    match other.into_iter() {
                        Ok(..) => {
                            let val = other.at(Value::new(idx));
                            idx += 1;
                            match val {
                                Ok(v) => {
                                    len = other.length()?;
                                    v.clone()
                                }
                                Err(..) => {
                                    return Err(ValueError::NotEnoughParametersForInterpolation);
                                }
                            }
                        }
                        Err(..) => {
                            if idx == 0 {
                                idx += 1;
                                len = 1;
                                other.clone()
                            } else {
                                // We need more than one argument.
                                return Err(ValueError::NotEnoughParametersForInterpolation);
                            }
                        }
                    }
                };
                match chars.next() {
                    Some('s') => res += &var.to_str(),  // str(x)
                    Some('r') => res += &var.to_repr(), // repr(x)
                    // signed integer decimal
                    Some('d') | Some('i') => res += &var.to_int()?.to_string(),
                    // signed octal
                    Some('o') => {
                        let x = var.to_int()?;
                        res += &format!("{}{:o}", if x.is_negative() { "-" } else { "" }, x.abs());
                    }
                    // signed hexadecimal, lowercase
                    Some('x') => {
                        let x = var.to_int()?;
                        res += &format!("{}{:x}", if x.is_negative() { "-" } else { "" }, x.abs());
                    }
                    // signed hexadecimal, uppercase
                    Some('X') => {
                        let x = var.to_int()?;
                        res += &format!("{}{:X}", if x.is_negative() { "-" } else { "" }, x.abs());
                    }
                    // x for string, chr(x) for int
                    Some('c') => match var.get_type() {
                        "string" => {
                            if var.length()? != 1 {
                                return Err(ValueError::InterpolationValueNotChar);
                            } else {
                                res += &var.to_str();
                            }
                        }
                        _ => {
                            let codepoint = var.to_int()? as u32;
                            match std::char::from_u32(codepoint) {
                                Some(c) => res.push(c),
                                None => {
                                    return Err(ValueError::InterpolationValueNotInUTFRange(
                                        codepoint,
                                    ))
                                }
                            }
                        }
                    },
                    _ => return Err(ValueError::InterpolationFormat),
                }
                let s: String = chars.collect();
                res += &s;
            } else {
                last_percent = false;
                res += s;
            }
        }
        if idx < len {
            Err(ValueError::TooManyParametersForInterpolation)
        } else {
            Ok(Value::new(res))
        }
    }

    not_supported!(iterable);
    not_supported!(set_indexable);
    not_supported!(attr, function);
    not_supported!(plus, minus, sub, div, pipe, floor_div);
}

#[cfg(test)]
mod tests {
    use super::super::Value;
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_to_repr() {
        assert_eq!("'\\t\\n\\'\\\"'", Value::from("\t\n'\"").to_repr());
        assert_eq!("'Hello, 世界'", Value::from("Hello, 世界").to_repr());
    }

    #[test]
    fn test_string_len() {
        assert_eq!(1, Value::from("😿").length().unwrap())
    }

    #[test]
    fn test_arithmetic_on_string() {
        // "abc" + "def" = "abcdef"
        assert_eq!(
            Value::from("abc").add(Value::from("def")).unwrap(),
            Value::from("abcdef")
        );
        // "abc" * 3 == "abcabcabc"
        assert_eq!(
            Value::from("abc").mul(Value::from(3)).unwrap(),
            Value::from("abcabcabc")
        );
    }

    #[test]
    fn test_slice_string() {
        // Remove the first element: "abc"[1:] == "bc".
        assert_eq!(
            Value::from("abc")
                .slice(Some(Value::from(1)), None, None)
                .unwrap(),
            Value::from("bc")
        );
        // Remove the last element: "abc"[:-1] == "ab".
        assert_eq!(
            Value::from("abc")
                .slice(None, Some(Value::from(-1)), None)
                .unwrap(),
            Value::from("ab")
        );
        // Remove the first and the last element: "abc"[1:-1] == "b".
        assert_eq!(
            Value::from("abc")
                .slice(Some(Value::from(1)), Some(Value::from(-1)), None)
                .unwrap(),
            Value::from("b")
        );
        // Select one element out of 2, skipping the first: "banana"[1::2] == "aaa".
        assert_eq!(
            Value::from("banana")
                .slice(Some(Value::from(1)), None, Some(Value::from(2)))
                .unwrap(),
            Value::from("aaa")
        );
        // Select one element out of 2 in reverse order, starting at index 4:
        //   "banana"[4::-2] = "nnb"
        assert_eq!(
            Value::from("banana")
                .slice(Some(Value::from(4)), None, Some(Value::from(-2)))
                .unwrap(),
            Value::from("nnb")
        );
    }

    #[test]
    fn test_string_is_in() {
        // "a" in "abc" == True
        assert!(
            Value::from("abc")
                .is_in(&Value::from("a"))
                .unwrap()
                .to_bool()
        );
        // "b" in "abc" == True
        assert!(
            Value::from("abc")
                .is_in(&Value::from("b"))
                .unwrap()
                .to_bool()
        );
        // "z" in "abc" == False
        assert!(
            !Value::from("abc")
                .is_in(&Value::from("z"))
                .unwrap()
                .to_bool()
        );
    }

    #[test]
    fn test_string_interpolation() {
        // "Hello %s, your score is %d" % ("Bob", 75) == "Hello Bob, your score is 75"
        assert_eq!(
            Value::from("Hello %s, your score is %d")
                .percent(Value::from(("Bob", 75)))
                .unwrap(),
            Value::from("Hello Bob, your score is 75")
        );
        // "%d %o %x %c" % (65, 65, 65, 65) == "65 101 41 A"
        assert_eq!(
            Value::from("%d %o %x %c")
                .percent(Value::from((65, 65, 65, 65)))
                .unwrap(),
            Value::from("65 101 41 A")
        );
        // "%(greeting)s, %(audience)s" % {"greeting": "Hello", "audience": "world"} ==
        //      "Hello, world"
        let mut d = Value::from(HashMap::<Value, Value>::new());
        d.set_at(Value::from("greeting"), Value::from("Hello"))
            .unwrap();
        d.set_at(Value::from("audience"), Value::from("world"))
            .unwrap();
        assert_eq!(
            Value::from("%(greeting)s, %(audience)s")
                .percent(d)
                .unwrap(),
            Value::from("Hello, world")
        );
    }
}
