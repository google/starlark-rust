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
use crate::values::*;
use linked_hash_set::LinkedHashSet;
use std::borrow::BorrowMut;
use std::cmp::{Eq, Ordering, PartialEq};
use std::hash::{Hash, Hasher};
use std::num::Wrapping;

pub struct Set {
    mutability: IterableMutability,
    content: LinkedHashSet<ValueWrapper>,
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
            result
                .content
                .insert_if_absent(ValueWrapper::new(v.into())?);
        }
        Ok(Value::new(result))
    }

    pub fn insert_if_absent(set: &Value, v: Value) -> Result<Value, ValueError> {
        let v = v.clone_for_container_value(set)?;
        Self::mutate(set, &|hashset| {
            hashset.insert_if_absent(ValueWrapper::new(v.clone())?);
            Ok(Value::from(None))
        })
    }

    pub fn mutate(
        v: &Value,
        f: &Fn(&mut LinkedHashSet<ValueWrapper>) -> ValueResult,
    ) -> ValueResult {
        if v.get_type() != "set" {
            Err(ValueError::IncorrectParameterType)
        } else {
            let mut v = v.clone();
            v.downcast_apply_mut(|x: &mut Set| -> ValueResult {
                x.mutability.test()?;
                f(&mut x.content)
            })
        }
    }

    pub fn compare<Return>(
        v1: &Value,
        v2: &Value,
        f: &Fn(
            &LinkedHashSet<ValueWrapper>,
            &LinkedHashSet<ValueWrapper>,
        ) -> Result<Return, ValueError>,
    ) -> Result<Return, ValueError> {
        if v1.get_type() != "set" || v2.get_type() != "set" {
            Err(ValueError::IncorrectParameterType)
        } else {
            v1.downcast_apply(|v1: &Set| v2.downcast_apply(|v2: &Set| f(&v1.content, &v2.content)))
        }
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
            value.value.borrow_mut().freeze();
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
    fn to_str(&self) -> String {
        format!(
            "{{{}}}",
            self.content
                .iter()
                .map(|x| x.value.to_repr(),)
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                },)
        )
    }

    fn to_repr(&self) -> String {
        self.to_str()
    }

    not_supported!(to_int);
    fn get_type(&self) -> &'static str {
        "set"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn compare(&self, other: &TypedValue, _recursion: u32) -> Result<Ordering, ValueError> {
        if other.get_type() == "set" {
            let other = other.as_any().downcast_ref::<Self>().unwrap();
            if self
                .content
                .symmetric_difference(&other.content)
                .next()
                .is_none()
            {
                return Ok(Ordering::Equal);
            }
            // Consistent: Yes.
            // Useful: No.
            let l = self.get_hash().unwrap();
            let r = other.get_hash().unwrap();
            if l <= r {
                Ok(Ordering::Less)
            } else {
                Ok(Ordering::Greater)
            }
        } else {
            default_compare(self, other)
        }
    }

    fn at(&self, index: Value) -> ValueResult {
        let i = index.convert_index(self.length()?)? as usize;
        let to_skip = if i == 0 { 0 } else { i - 1 };
        Ok(self.content.iter().nth(to_skip).unwrap().value.clone())
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content.len() as i64)
    }

    fn is_in(&self, other: &Value) -> ValueResult {
        Ok(Value::new(
            self.content.contains(&ValueWrapper::new(other.clone())?),
        ))
    }

    fn is_descendant(&self, other: &TypedValue) -> bool {
        self.content
            .iter()
            .any(|x| x.value.same_as(other) || x.value.is_descendant(other))
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
            self.content.iter().map(|v| &v.value),
        )))
    }

    fn iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError> {
        Ok(Box::new(self.content.iter().map(|x| x.value.clone())))
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
                    .insert_if_absent(ValueWrapper::new(x.clone())?);
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
            .map(|v| v.precomputed_hash)
            .map(Wrapping)
            .fold(Wrapping(0_u64), |acc, v| acc + v)
            .0)
    }

    not_supported!(mul, set_at);
    not_supported!(attr, function);
    not_supported!(plus, minus, sub, div, pipe, percent, floor_div);
}

#[derive(Clone)]
pub struct ValueWrapper {
    pub value: Value,
    // Precompute the hash to verify that the value is hashable. Eagerly error if it's not, so that
    // the caller who wants to use the ValueWrapper knows it can't be done.
    precomputed_hash: u64,
}

impl ValueWrapper {
    pub fn new(value: Value) -> Result<ValueWrapper, ValueError> {
        let precomputed_hash = value.get_hash()?;
        Ok(ValueWrapper {
            value,
            precomputed_hash,
        })
    }
}

impl Into<Value> for &ValueWrapper {
    fn into(self) -> Value {
        self.clone().value
    }
}

impl PartialEq for ValueWrapper {
    fn eq(&self, other: &ValueWrapper) -> bool {
        self.value.compare(&other.value, 0) == Ok(Ordering::Equal)
    }
}

impl Eq for ValueWrapper {}

impl Hash for ValueWrapper {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_u64(self.precomputed_hash);
    }
}

impl Into<Value> for ValueWrapper {
    fn into(self) -> Value {
        self.value
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
