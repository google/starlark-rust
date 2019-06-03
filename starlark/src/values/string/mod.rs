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
use crate::values::error::ValueError;
use crate::values::string::interpolation::ArgsFormat;
use crate::values::*;
use std;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub mod interpolation;
use std::iter;

impl TypedValue for String {
    type Holder = Immutable<String>;

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(iter::empty())
    }

    fn to_str(&self) -> String {
        self.clone()
    }
    fn to_repr(&self) -> String {
        format!(
            "\"{}\"",
            self.chars()
                .map(|x| -> String { x.escape_debug().collect() })
                .fold("".to_string(), |accum, s| accum + &s)
        )
    }

    const TYPE: &'static str = "string";
    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        let mut s = DefaultHasher::new();
        self.hash(&mut s);
        Ok(s.finish())
    }

    fn equals(&self, other: &String) -> Result<bool, ValueError> {
        Ok(*self == *other)
    }

    fn compare(&self, other: &String) -> Result<Ordering, ValueError> {
        Ok(self.cmp(&other.to_str()))
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.len() as i64)? as usize;
        Ok(Value::new(self.chars().nth(i).unwrap().to_string()))
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.chars().count() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        if other.get_type() == "string" {
            Ok(self.contains(&other.to_str()))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
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
    fn add(&self, other: &String) -> Result<String, ValueError> {
        Ok(self.chars().chain(other.to_str().chars()).collect())
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
    /// # use std::convert::TryFrom;
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
    /// let mut d = Value::try_from(HashMap::<String, Value>::new()).unwrap();
    /// d.set_at(Value::from("greeting"), Value::from("Hello"));
    /// d.set_at(Value::from("audience"), Value::from("world"));
    /// # assert!(
    /// Value::from("%(greeting)s, %(audience)s").percent(d).unwrap() == Value::from("Hello, world")
    /// # );
    /// ```
    fn percent(&self, other: Value) -> ValueResult {
        Ok(Value::new(ArgsFormat::parse(&self)?.format(other)?))
    }
}

impl From<String> for Value {
    fn from(s: String) -> Self {
        Value::new(s)
    }
}

impl<'a> From<&'a str> for Value {
    fn from(a: &'a str) -> Value {
        Value::new(a.to_owned())
    }
}

#[cfg(test)]
mod tests {
    use super::super::Value;

    #[test]
    fn test_to_repr() {
        assert_eq!("\"\\t\\n\\'\\\"\"", Value::from("\t\n'\"").to_repr());
        assert_eq!("\"Hello, 世界\"", Value::from("Hello, 世界").to_repr());
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
        assert!(Value::from("abc").is_in(&Value::from("a")).unwrap());
        // "b" in "abc" == True
        assert!(Value::from("abc").is_in(&Value::from("b")).unwrap());
        // "z" in "abc" == False
        assert!(!Value::from("abc").is_in(&Value::from("z")).unwrap());
    }
}
