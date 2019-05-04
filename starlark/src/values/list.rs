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

//! Define the list type of Starlark
use crate::values::immutable::ReadableContent;
use crate::values::mutable::{Mutable, MutableContent};
use crate::values::*;
use std::cmp::Ordering;

impl ReadableContent for Vec<Value> {
    fn get_type() -> &'static str {
        "list"
    }

    fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item = Value> + 'a> {
        Box::new(self.as_slice().iter().cloned())
    }

    /// Returns a string representation for the list
    ///
    /// # Examples:
    /// ```
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// assert_eq!("[1, 2, 3]", Value::from(vec![1, 2, 3]).to_str());
    /// assert_eq!("[1, [2, 3]]",
    ///            Value::from(vec![Value::from(1), Value::from(vec![2, 3])]).to_str());
    /// assert_eq!("[1]", Value::from(vec![1]).to_str());
    /// assert_eq!("[]", Value::from(Vec::<i64>::new()).to_str());
    /// ```
    fn to_repr(&self) -> String {
        format!(
            "[{}]",
            self.as_slice().iter().map(Value::to_repr).enumerate().fold(
                "".to_string(),
                |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },
            )
        )
    }

    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn at(&self, index: Value) -> Result<Value, ValueError> {
        let i = index.convert_index(self.length()?)? as usize;
        Ok(self[i].clone())
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        for x in self {
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
        Ok(Value::from(tuple::slice_vector(
            start,
            stop,
            stride,
            self.as_slice().iter(),
        )))
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.len() as i64)
    }

    fn iter(&self) -> Result<Vec<Value>, ValueError> {
        Ok(self.clone())
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a list.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// # assert!(
    /// // [1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
    /// Value::from(vec![1,2,3]).add(Value::from(vec![2,3])).unwrap()
    ///     == Value::from(vec![1, 2, 3, 2, 3])
    /// # );
    /// ```
    fn add(&self, other: &Self) -> Result<Self, ValueError> {
        let mut result = Vec::with_capacity(self.len() + other.len());
        result.extend(self.as_slice().iter().cloned());
        result.extend(other.as_slice().iter().cloned());
        Ok(result)
    }

    /// Repeat `other` times this tuple.
    ///
    /// `other` has to be an int or a boolean.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// # assert!(
    /// // [1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
    /// Value::from(vec![1,2,3]).mul(Value::from(3)).unwrap()
    ///              == Value::from(vec![1, 2, 3, 1, 2, 3, 1, 2, 3])
    /// # );
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        if other.get_type() == "int" || other.get_type() == "boolean" {
            let l = other.to_int()?;
            let mut result = Vec::new();
            for _i in 0..l {
                for x in self {
                    result.push(x.clone());
                }
            }
            Ok(Value::new(List::new(result)))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    fn compare(&self, other: &Self, recursion: u32) -> Result<Ordering, ValueError> {
        let mut iter1 = self.iter()?.into_iter();
        let mut iter2 = other.iter()?.into_iter();
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

    not_supported!(get_hash);
    not_supported!(arithmetic);
    not_supported!(to_int, pipe, attr, function, percent);
}

impl MutableContent for Vec<Value> {
    fn set_at_check(&self, _index: &Value) -> Result<(), ValueError> {
        Ok(())
    }

    /// Set the value at `index` to `new_value`
    ///
    /// # Example
    /// ```
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// let mut v = Value::from(vec![1, 2, 3]);
    /// v.set_at(Value::from(1), Value::from(1)).unwrap();
    /// v.set_at(Value::from(2), Value::from(vec![2, 3])).unwrap();
    /// assert_eq!(&v.to_repr(), "[1, 1, [2, 3]]");
    /// ```
    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        let i = index.convert_index(self.length()?)? as usize;
        self[i] = new_value;
        Ok(())
    }

    not_supported!(set_attr);
}

pub type List = Mutable<Vec<Value>>;

impl<T: Into<Value> + Clone> From<Vec<T>> for List {
    fn from(a: Vec<T>) -> List {
        let mut result = Vec::new();
        for x in a.iter() {
            let v: Value = x.clone().into();
            result.push(v);
        }
        List::new(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_str() {
        assert_eq!("[1, 2, 3]", Value::from(vec![1, 2, 3]).to_str());
        assert_eq!(
            "[1, [2, 3]]",
            Value::from(vec![Value::from(1), Value::from(vec![2, 3])]).to_str()
        );
        assert_eq!("[1]", Value::from(vec![1]).to_str());
        assert_eq!("[]", Value::from(Vec::<i64>::new()).to_str());
    }

    #[test]
    fn test_mutate_list() {
        let mut v = Value::from(vec![1, 2, 3]);
        v.set_at(Value::from(1), Value::from(1)).unwrap();
        v.set_at(Value::from(2), Value::from(vec![2, 3])).unwrap();
        assert_eq!(&v.to_repr(), "[1, 1, [2, 3]]");
    }

    #[test]
    fn test_arithmetic_on_list() {
        // [1, 2, 3] + [2, 3] == [1, 2, 3, 2, 3]
        assert_eq!(
            Value::from(vec![1, 2, 3])
                .add(Value::from(vec![2, 3]))
                .unwrap(),
            Value::from(vec![1, 2, 3, 2, 3])
        );
        // [1, 2, 3] * 3 == [1, 2, 3, 1, 2, 3, 1, 2, 3]
        assert_eq!(
            Value::from(vec![1, 2, 3]).mul(Value::from(3)).unwrap(),
            Value::from(vec![1, 2, 3, 1, 2, 3, 1, 2, 3])
        );
    }

    #[test]
    fn test_value_alias() {
        let v1 = Value::from(vec![1, 2, 3]);
        let mut v2 = v1.clone();
        v2.set_at(Value::from(2), Value::from(4)).unwrap();
        assert_eq!(v2.to_str(), "[1, 2, 4]");
        assert_eq!(v1.to_str(), "[1, 2, 4]");
    }

    #[test]
    fn test_is_descendant() {
        let v1 = Value::from(vec![1, 2, 3]);
        let v2 = Value::from(vec![Value::new_imm(1), Value::new_imm(2), v1.clone()]);
        let v3 = Value::from(vec![Value::new_imm(1), Value::new_imm(2), v2.clone()]);
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
