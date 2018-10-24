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

//! Define the tuple type for Starlark.
use std::borrow::BorrowMut;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;
use values::*;

/// A starlark tuple
pub struct Tuple {
    content: Vec<Value>,
}

#[doc(hidden)]
pub fn slice_vector(start: i64, stop: i64, stride: i64, content: &Vec<Value>) -> Vec<Value> {
    let (low, take, astride) = if stride < 0 {
        (stop + 1, start - stop, -stride)
    } else {
        (start, stop - start, stride)
    };
    if take <= 0 {
        return Vec::new();
    }
    let mut v: Vec<Value> = content
        .iter()
        .skip(low as usize)
        .take(take as usize)
        .map(|x| x.clone())
        .collect();
    if stride < 0 {
        v.reverse();
    }
    v.into_iter()
        .enumerate()
        .filter_map(|x| {
            if 0 == (x.0 as i64 % astride) {
                Some(x.1)
            } else {
                None
            }
        })
        .collect()
}

impl Tuple {
    pub fn new(values: &[Value]) -> Value {
        let mut result = Tuple {
            content: Vec::new(),
        };
        for x in values.iter() {
            result.content.push(x.clone());
        }
        Value::new(result)
    }
}

impl From<()> for Tuple {
    fn from(_a: ()) -> Tuple {
        Tuple { content: vec![] }
    }
}

// TODO: Can we do that with macro? i.e. generating the index number automatically?
impl<T: Into<Value>> From<(T,)> for Tuple {
    fn from(a: (T,)) -> Tuple {
        Tuple {
            content: vec![a.0.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>> From<(T1, T2)> for Tuple {
    fn from(a: (T1, T2)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>> From<(T1, T2, T3)> for Tuple {
    fn from(a: (T1, T2, T3)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into(), a.2.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>> From<(T1, T2, T3, T4)>
    for Tuple
{
    fn from(a: (T1, T2, T3, T4)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into(), a.2.into(), a.3.into()],
        }
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>, T5: Into<Value>>
    From<(T1, T2, T3, T4, T5)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5)) -> Tuple {
        Tuple {
            content: vec![a.0.into(), a.1.into(), a.2.into(), a.3.into(), a.4.into()],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
        T8: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7, T8)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7, T8)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
                a.7.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
        T8: Into<Value>,
        T9: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7, T8, T9)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7, T8, T9)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
                a.7.into(),
                a.8.into(),
            ],
        }
    }
}

impl<
        T1: Into<Value>,
        T2: Into<Value>,
        T3: Into<Value>,
        T4: Into<Value>,
        T5: Into<Value>,
        T6: Into<Value>,
        T7: Into<Value>,
        T8: Into<Value>,
        T9: Into<Value>,
        T10: Into<Value>,
    > From<(T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5, T6, T7, T8, T9, T10)) -> Tuple {
        Tuple {
            content: vec![
                a.0.into(),
                a.1.into(),
                a.2.into(),
                a.3.into(),
                a.4.into(),
                a.5.into(),
                a.6.into(),
                a.7.into(),
                a.8.into(),
                a.9.into(),
            ],
        }
    }
}

impl TypedValue for Tuple {
    any!();

    fn immutable(&self) -> bool {
        true
    }
    fn freeze(&mut self) {
        // Tuple are weird, immutable but with potentially mutable
        for x in self.content.iter_mut() {
            x.borrow_mut().freeze();
        }
    }

    fn to_str(&self) -> String {
        format!(
            "({}{})",
            self.content.iter().map(|x| x.to_repr(),).enumerate().fold(
                "".to_string(),
                |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },
            ),
            if self.content.len() == 1 { "," } else { "" }
        )
    }

    fn to_repr(&self) -> String {
        self.to_str()
    }

    not_supported!(to_int);
    fn get_type(&self) -> &'static str {
        "tuple"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        let mut s = DefaultHasher::new();
        for v in self.content.iter() {
            s.write_u64(v.get_hash()?)
        }
        Ok(s.finish())
    }

    fn compare(&self, other: &Value, recursion: u32) -> Result<Ordering, ValueError> {
        if other.get_type() == "tuple" {
            let mut iter1 = self.into_iter()?;
            let mut iter2 = other.into_iter()?;
            loop {
                match (iter1.next(), iter2.next()) {
                    (None, None) => return Ok(Ordering::Equal),
                    (None, Some(..)) => return Ok(Ordering::Less),
                    (Some(..), None) => return Ok(Ordering::Greater),
                    (Some(v1), Some(v2)) => {
                        let r = v1.compare(&v2, recursion + 1)?;
                        if r != Ordering::Equal {
                            return Ok(r);
                        }
                    }
                }
            }
        } else {
            default_compare(self, other)
        }
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.length()?)? as usize;
        Ok(self.content[i].clone())
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content.len() as i64)
    }

    fn is_in(&self, other: &Value) -> ValueResult {
        for x in self.content.iter() {
            if x.compare(other, 0)? == Ordering::Equal {
                return Ok(Value::new(true));
            }
        }
        Ok(Value::new(false))
    }

    fn is_descendant(&self, other: &TypedValue) -> bool {
        self.content
            .iter()
            .any(|x| x.same_as(other) || x.is_descendant(other))
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        let (start, stop, stride) =
            Value::convert_slice_indices(self.length()?, start, stop, stride)?;
        Ok(Tuple::new(&slice_vector(
            start,
            stop,
            stride,
            &self.content,
        )))
    }

    fn into_iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError> {
        Ok(Box::new(self.content.iter().map(|x| x.clone())))
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a tuple.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::tuple::Tuple;
    /// # assert!(
    /// // (1, 2, 3) + (2, 3) == (1, 2, 3, 2, 3)
    /// Value::from((1,2,3)).add(Value::from((2,3))).unwrap() == Value::from((1, 2, 3, 2, 3))
    /// # );
    /// ```
    fn add(&self, other: Value) -> ValueResult {
        if other.get_type() == "tuple" {
            let mut result = Tuple {
                content: Vec::new(),
            };
            for x in self.content.iter() {
                result.content.push(x.clone());
            }
            for x in other.into_iter()? {
                result.content.push(x.clone());
            }
            Ok(Value::new(result))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    /// Repeat `other` times this tuple.
    ///
    /// `other` has to be an int or a boolean.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::tuple::Tuple;
    /// # assert!(
    /// // (1, 2, 3) * 3 == (1, 2, 3, 1, 2, 3, 1, 2, 3)
    /// Value::from((1,2,3)).mul(Value::from(3)).unwrap()
    ///              == Value::from((1, 2, 3, 1, 2, 3, 1, 2, 3))
    /// # );
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        if other.get_type() == "int" || other.get_type() == "boolean" {
            let l = other.to_int()?;
            let mut result = Tuple {
                content: Vec::new(),
            };
            for _i in 0..l {
                for x in self.content.iter() {
                    result.content.push(x.clone());
                }
            }
            Ok(Value::new(result))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    not_supported!(set_indexable);
    not_supported!(attr, function);
    not_supported!(plus, minus, sub, div, pipe, percent, floor_div);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_str() {
        assert_eq!("(1, 2, 3)", Value::from((1, 2, 3)).to_str());
        assert_eq!("(1, (2, 3))", Value::from((1, (2, 3))).to_str());
        assert_eq!("(1,)", Value::from((1,)).to_str());
        assert_eq!("()", Value::from(()).to_str());
    }

    #[test]
    fn test_arithmetic_on_tuple() {
        // (1, 2, 3) + (2, 3) == (1, 2, 3, 2, 3)
        assert_eq!(
            Value::from((1, 2, 3)).add(Value::from((2, 3))).unwrap(),
            Value::from((1, 2, 3, 2, 3))
        );
        // (1, 2, 3) * 3 == (1, 2, 3, 1, 2, 3, 1, 2, 3)
        assert_eq!(
            Value::from((1, 2, 3)).mul(Value::from(3)).unwrap(),
            Value::from((1, 2, 3, 1, 2, 3, 1, 2, 3))
        );
    }

    #[test]
    fn test_is_descendant() {
        let v1 = Value::from((1, 2, 3));
        let v2 = Value::from((1, 2, v1.clone()));
        let v3 = Value::from((1, 2, v2.clone()));
        assert!(v3.is_descendant_value(&v2));
        assert!(v3.is_descendant_value(&v1));
        assert!(v3.is_descendant_value(&v3));

        assert!(v2.is_descendant_value(&v1));
        assert!(v2.is_descendant_value(&v2));
        assert!(!v2.is_descendant_value(&v3));

        assert!(v1.is_descendant_value(&v1));
        assert!(!v1.is_descendant_value(&v2));
        assert!(!v1.is_descendant_value(&v3));
    }
}
