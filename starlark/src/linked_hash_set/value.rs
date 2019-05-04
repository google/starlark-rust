// Copyright 2019 The Starlark in Rust Authors
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

//! Define the set type of Starlark
use std::cmp::Ordering;
use std::num::Wrapping;

use linked_hash_set::LinkedHashSet;

use crate::values::hashed_value::HashedValue;
use crate::values::immutable::ReadableContent;
use crate::values::mutable::{Mutable, MutableContent};
use crate::values::*;

impl ReadableContent for LinkedHashSet<HashedValue> {
    fn get_type() -> &'static str {
        "set"
    }

    fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item = Value> + 'a> {
        Box::new(self.iter().map(|v| v.get_value().clone()))
    }

    /// Returns a string representation for the set
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
            "{{{}}}",
            self.iter()
                .map(|x| x.get_value().to_repr(),)
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },)
        )
    }

    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.length()?)? as usize;
        let to_skip = if i == 0 { 0 } else { i - 1 };
        Ok(self.iter().nth(to_skip).unwrap().get_value().clone())
    }

    fn compare(
        &self,
        other: &LinkedHashSet<HashedValue>,
        _recursion: u32,
    ) -> Result<Ordering, ValueError> {
        if self.symmetric_difference(other).next().is_none() {
            return Ok(Ordering::Equal);
        }
        // Comparing based on hash value isn't particularly meaningful to users, who may expect
        // sets to compare based on, say, their size, or comparing their elements.
        // We do this because it's guaranteed to provide a consistent ordering for any pair of
        // sets. We should consider better defining the sort order of sets if users complain.
        let l = self.get_hash()?;
        let r = other.get_hash()?;
        if l <= r {
            Ok(Ordering::Less)
        } else {
            Ok(Ordering::Greater)
        }
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        Ok(self.contains(&HashedValue::new(other.clone())?))
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(self
            .iter()
            .map(HashedValue::get_hash)
            .map(Wrapping)
            .fold(Wrapping(0_u64), |acc, v| acc + v)
            .0)
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
            self.iter().map(HashedValue::get_value),
        )))
    }

    fn iter(&self) -> Result<Vec<Value>, ValueError> {
        Ok(self.iter().map(|x| x.get_value().clone()).collect())
    }

    /// Concatenate `other` to the current value.
    ///
    /// `other` has to be a set.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::list::List;
    /// # assert!(
    /// // {1, 2, 3} + {2, 3, 4} == {1, 2, 3, 4}
    /// Value::from(vec![1,2,3]).add(Value::from(vec![2,3])).unwrap()
    ///     == Value::from(vec![1, 2, 3, 2, 3])
    /// # );
    /// ```
    fn add(
        &self,
        other: &LinkedHashSet<HashedValue>,
    ) -> Result<LinkedHashSet<HashedValue>, ValueError> {
        let mut result = self.clone();
        for x in other.iter() {
            result.insert_if_absent(x.clone());
        }
        Ok(result)
    }

    not_supported!(mul, percent, function);
    not_supported!(arithmetic);
    not_supported!(to_int, pipe);
    not_supported!(attr);
}

impl MutableContent for LinkedHashSet<HashedValue> {
    not_supported!(set_at, set_attr);
}

pub type Set = Mutable<LinkedHashSet<HashedValue>>;

impl Set {
    pub fn from<V: Into<Value>>(values: Vec<V>) -> Result<Value, ValueError> {
        let mut result = LinkedHashSet::new();
        for v in values.into_iter() {
            result.insert_if_absent(HashedValue::new(v.into())?);
        }
        Ok(Value::new(Set::new(result)))
    }

    pub fn insert_if_absent(set: &Value, v: Value) -> Result<Value, ValueError> {
        let v = v.clone_for_container_value(set)?;
        Self::mutate(set, &|hashset| {
            hashset.insert_if_absent(HashedValue::new(v.clone())?);
            Ok(Value::from(None))
        })
    }

    pub fn compare<Return>(
        v1: &Value,
        v2: &Value,
        f: &Fn(
            &LinkedHashSet<HashedValue>,
            &LinkedHashSet<HashedValue>,
        ) -> Result<Return, ValueError>,
    ) -> Result<Return, ValueError> {
        v1.downcast_apply(|v1: &Set| {
            v2.downcast_apply(|v2: &Set| f(&v1.content.borrow(), &v2.content.borrow()))
                .unwrap_or(Err(ValueError::IncorrectParameterType))
        })
        .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl From<LinkedHashSet<HashedValue>> for Value {
    fn from(set: LinkedHashSet<HashedValue>) -> Value {
        Value::new(Set::new(set))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_str() {
        assert_eq!("{1, 2, 3}", Set::from(vec![1, 2, 3]).unwrap().to_str());
        assert_eq!(
            "{1, {2, 3}}",
            Set::from(vec![Value::from(1), Set::from(vec![2, 3]).unwrap()])
                .unwrap()
                .to_str()
        );
        assert_eq!("{1}", Set::from(vec![1]).unwrap().to_str());
        assert_eq!("{}", Set::from(Vec::<i64>::new()).unwrap().to_str());
    }

    #[test]
    fn equality_ignores_order() {
        assert_eq!(
            Set::from(vec![1, 2, 3]).unwrap(),
            Set::from(vec![3, 2, 1]).unwrap(),
        );
    }

    #[test]
    fn test_value_alias() {
        let v1 = Set::from(vec![1, 2]).unwrap();
        let v2 = v1.clone();
        Set::insert_if_absent(&v2, Value::from(3)).unwrap();
        assert_eq!(v2.to_str(), "{1, 2, 3}");
        assert_eq!(v1.to_str(), "{1, 2, 3}");
    }

    #[test]
    fn test_is_descendant() {
        let v1 = Set::from(vec![1, 2, 3]).unwrap();
        let v2 = Set::from(vec![Value::new_imm(1), Value::new_imm(2), v1.clone()]).unwrap();
        let v3 = Set::from(vec![Value::new_imm(1), Value::new_imm(2), v2.clone()]).unwrap();
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
