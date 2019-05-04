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
use crate::values::immutable::{Immutable, ImmutableContent, ReadableContent};
use crate::values::*;
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::Hasher;

// Need to wrap `Vec<Value>` in a struct,
// because there's `impl ImmutableContent for Vec<Value>` for `list`.
pub struct TupleContent(Vec<Value>);

/// A starlark tuple
pub type Tuple = Immutable<TupleContent>;

#[doc(hidden)]
pub fn slice_vector<'a, I: Iterator<Item = &'a Value>>(
    start: i64,
    stop: i64,
    stride: i64,
    content: I,
) -> Vec<Value> {
    let (low, take, astride) = if stride < 0 {
        (stop + 1, start - stop, -stride)
    } else {
        (start, stop - start, stride)
    };
    if take <= 0 {
        return Vec::new();
    }
    let mut v: Vec<Value> = content
        .skip(low as usize)
        .take(take as usize)
        .cloned()
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

impl From<()> for Tuple {
    fn from(_a: ()) -> Tuple {
        Tuple::new(TupleContent(vec![]))
    }
}

// TODO: Can we do that with macro? i.e. generating the index number automatically?
impl<T: Into<Value>> From<(T,)> for Tuple {
    fn from(a: (T,)) -> Tuple {
        Tuple::new(TupleContent(vec![a.0.into()]))
    }
}

impl<T1: Into<Value>, T2: Into<Value>> From<(T1, T2)> for Tuple {
    fn from(a: (T1, T2)) -> Tuple {
        Tuple::new(TupleContent(vec![a.0.into(), a.1.into()]))
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>> From<(T1, T2, T3)> for Tuple {
    fn from(a: (T1, T2, T3)) -> Tuple {
        Tuple::new(TupleContent(vec![a.0.into(), a.1.into(), a.2.into()]))
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>> From<(T1, T2, T3, T4)>
    for Tuple
{
    fn from(a: (T1, T2, T3, T4)) -> Tuple {
        Tuple::new(TupleContent(vec![
            a.0.into(),
            a.1.into(),
            a.2.into(),
            a.3.into(),
        ]))
    }
}

impl<T1: Into<Value>, T2: Into<Value>, T3: Into<Value>, T4: Into<Value>, T5: Into<Value>>
    From<(T1, T2, T3, T4, T5)> for Tuple
{
    fn from(a: (T1, T2, T3, T4, T5)) -> Tuple {
        Tuple::new(TupleContent(vec![
            a.0.into(),
            a.1.into(),
            a.2.into(),
            a.3.into(),
            a.4.into(),
        ]))
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
        Tuple::new(TupleContent(vec![
            a.0.into(),
            a.1.into(),
            a.2.into(),
            a.3.into(),
            a.4.into(),
            a.5.into(),
        ]))
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
        Tuple::new(TupleContent(vec![
            a.0.into(),
            a.1.into(),
            a.2.into(),
            a.3.into(),
            a.4.into(),
            a.5.into(),
            a.6.into(),
        ]))
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
        Tuple::new(TupleContent(vec![
            a.0.into(),
            a.1.into(),
            a.2.into(),
            a.3.into(),
            a.4.into(),
            a.5.into(),
            a.6.into(),
            a.7.into(),
        ]))
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
        Tuple::new(TupleContent(vec![
            a.0.into(),
            a.1.into(),
            a.2.into(),
            a.3.into(),
            a.4.into(),
            a.5.into(),
            a.6.into(),
            a.7.into(),
            a.8.into(),
        ]))
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
        Tuple::new(TupleContent(vec![
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
        ]))
    }
}

impl<T: Into<Value>> From<Vec<T>> for Tuple {
    fn from(v: Vec<T>) -> Tuple {
        Tuple::new(TupleContent(
            v.into_iter().map(T::into).collect::<Vec<Value>>(),
        ))
    }
}

impl ImmutableContent for TupleContent {}

impl ReadableContent for TupleContent {
    fn to_str(&self) -> String {
        format!(
            "({}{})",
            self.0
                .as_slice()
                .iter()
                .map(Value::to_repr)
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },),
            if self.0.len() == 1 { "," } else { "" }
        )
    }

    fn to_repr(&self) -> String {
        self.to_str()
    }

    not_supported!(to_int);
    fn get_type() -> &'static str {
        "tuple"
    }
    fn to_bool(&self) -> bool {
        !self.0.is_empty()
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        let mut s = DefaultHasher::new();
        for v in &self.0 {
            s.write_u64(v.get_hash()?)
        }
        Ok(s.finish())
    }

    fn compare(&self, other: &TupleContent, recursion: u32) -> Result<Ordering, ValueError> {
        let mut iter1 = self.0.as_slice().iter();
        let mut iter2 = other.0.as_slice().iter();
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
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.length()?)? as usize;
        Ok(self.0[i].clone())
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.0.len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        for x in self.0.as_slice().iter() {
            if x.compare(other, 0)? == Ordering::Equal {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        let (start, stop, stride) =
            Value::convert_slice_indices(self.length()?, start, stop, stride)?;
        Ok(Value::new(Tuple::new(TupleContent(slice_vector(
            start,
            stop,
            stride,
            self.0.as_slice().iter(),
        )))))
    }

    fn iter(&self) -> Result<Vec<Value>, ValueError> {
        Ok(self.0.clone())
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
    fn add(&self, other: &TupleContent) -> Result<TupleContent, ValueError> {
        let mut result = Vec::new();
        for x in self.0.as_slice().iter() {
            result.push(x.clone());
        }
        for x in other.0.as_slice().iter() {
            result.push(x.clone());
        }
        Ok(TupleContent(result))
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
            let mut result = Vec::new();
            for _i in 0..l {
                for x in &self.0 {
                    result.push(x.clone());
                }
            }
            Ok(Value::new(Tuple::new(TupleContent(result))))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    not_supported!(attr, function);
    not_supported!(plus, minus, sub, div, pipe, percent, floor_div);

    fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item = Value> + 'a> {
        Box::new(self.0.as_slice().iter().cloned())
    }
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
