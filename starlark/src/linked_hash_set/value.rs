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
use crate::linked_hash_set::set_impl::LinkedHashSet;
use crate::values::error::ValueError;
use crate::values::hashed_value::HashedValue;
use crate::values::*;
use std::cmp::Ordering;
use std::num::Wrapping;

pub(crate) struct Set {
    mutability: IterableMutability,
    content: LinkedHashSet<HashedValue>,
}

impl Default for Set {
    fn default() -> Self {
        Set {
            mutability: IterableMutability::Mutable,
            content: LinkedHashSet::new(),
        }
    }
}

impl Set {
    pub fn empty() -> Value {
        Value::new(Set::default())
    }

    pub fn from<V: Into<Value>>(values: Vec<V>) -> Result<Value, ValueError> {
        let mut result = Self::default();
        for v in values.into_iter() {
            result.content.insert_if_absent(HashedValue::new(v.into())?);
        }
        Ok(Value::new(result))
    }

    pub fn insert_if_absent(&mut self, v: Value) -> Result<(), ValueError> {
        let v = v.clone_for_container(self)?;
        self.content.insert_if_absent(HashedValue::new(v.clone())?);
        Ok(())
    }

    pub fn compare<Return>(
        v1: &Value,
        v2: &Value,
        f: &Fn(
            &LinkedHashSet<HashedValue>,
            &LinkedHashSet<HashedValue>,
        ) -> Result<Return, ValueError>,
    ) -> Result<Return, ValueError> {
        match (v1.downcast_ref::<Set>(), v2.downcast_ref::<Set>()) {
            (Some(v1), Some(v2)) => f(&v1.content, &v2.content),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub(crate) fn get_content(&self) -> &LinkedHashSet<HashedValue> {
        &self.content
    }

    pub fn clear(&mut self) {
        self.content.clear();
    }

    pub fn copy(&self) -> Set {
        Set {
            mutability: IterableMutability::Mutable,
            content: self.content.clone(),
        }
    }

    pub fn remove(&mut self, needle: &Value) -> Result<bool, ValueError> {
        let needle = HashedValue::new(needle.clone())?;
        Ok(self.content.remove(&needle))
    }

    pub fn insert(&mut self, value: Value) -> Result<(), ValueError> {
        let value = value.clone_for_container(self)?;
        let value = HashedValue::new(value)?;
        self.content.insert(value);
        Ok(())
    }

    pub fn pop_front(&mut self) -> Option<Value> {
        self.content.pop_front().map(HashedValue::into)
    }

    pub fn pop_back(&mut self) -> Option<Value> {
        self.content.pop_back().map(HashedValue::into)
    }

    pub fn len(&self) -> usize {
        self.content.len()
    }
}

impl From<Set> for Value {
    fn from(set: Set) -> Self {
        Value::new(set)
    }
}

impl TypedValue for Set {
    any!();

    define_iterable_mutability!(mutability);

    fn freeze(&mut self) {
        self.mutability.freeze();
        let mut new = LinkedHashSet::with_capacity(self.content.len());
        while !self.content.is_empty() {
            let mut value = self.content.pop_front().unwrap();
            value.freeze();
            new.insert(value);
        }
        self.content = new;
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
            self.content
                .iter()
                .map(|x| x.get_value().to_repr(),)
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },)
        )
    }

    fn get_type(&self) -> &'static str {
        "set"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn compare(&self, other: &Value, _recursion: u32) -> Result<Ordering, ValueError> {
        let other = other.downcast_ref::<Self>().unwrap();
        if self
            .content
            .symmetric_difference(&other.content)
            .next()
            .is_none()
        {
            return Ok(Ordering::Equal);
        }
        // Comparing based on hash value isn't particularly meaningful to users, who may expect
        // sets to compare based on, say, their size, or comparing their elements.
        // We do this because it's guaranteed to provide a consistent ordering for any pair of
        // sets. We should consider better defining the sort order of sets if users complain.
        let l = self.get_hash().unwrap();
        let r = other.get_hash().unwrap();
        if l <= r {
            Ok(Ordering::Less)
        } else {
            Ok(Ordering::Greater)
        }
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.length()?)? as usize;
        let to_skip = if i == 0 { 0 } else { i - 1 };
        Ok(self
            .content
            .iter()
            .nth(to_skip)
            .unwrap()
            .get_value()
            .clone())
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content.len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        Ok(self.content.contains(&HashedValue::new(other.clone())?))
    }

    fn is_descendant(&self, other: &TypedValue) -> bool {
        self.content
            .iter()
            .any(|x| x.get_value().same_as(other) || x.get_value().is_descendant(other))
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
            self.content.iter().map(HashedValue::get_value),
        )))
    }

    fn iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError> {
        Ok(Box::new(self.content.iter().map(|x| x.get_value().clone())))
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
    fn add(&self, other: Value) -> ValueResult {
        if other.get_type() == "set" {
            let mut result = Set {
                mutability: IterableMutability::Mutable,
                content: LinkedHashSet::new(),
            };
            for x in self.content.iter() {
                result.content.insert(x.clone());
            }
            for x in other.iter()? {
                result
                    .content
                    .insert_if_absent(HashedValue::new(x.clone())?);
            }
            Ok(Value::new(result))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(self
            .content
            .iter()
            .map(HashedValue::get_hash)
            .map(Wrapping)
            .fold(Wrapping(0_u64), |acc, v| acc + v)
            .0)
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
        v2.downcast_mut::<Set>()
            .unwrap()
            .unwrap()
            .insert_if_absent(Value::from(3))
            .unwrap();
        assert_eq!(v2.to_str(), "{1, 2, 3}");
        assert_eq!(v1.to_str(), "{1, 2, 3}");
    }

    #[test]
    fn test_is_descendant() {
        let v1 = Set::from(vec![1, 2, 3]).unwrap();
        let v2 = Set::from(vec![Value::new(1), Value::new(2), v1.clone()]).unwrap();
        let v3 = Set::from(vec![Value::new(1), Value::new(2), v2.clone()]).unwrap();
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
