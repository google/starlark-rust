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

//! Module define the Starlark type Dictionary
use crate::values::hashed_value::HashedValue;
use crate::values::immutable::ReadableContent;
use crate::values::mutable::{Mutable, MutableContent};
use crate::values::*;
use linked_hash_map::LinkedHashMap; // To preserve insertion order
use std::cmp::Ordering;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::hash::Hash;

impl ReadableContent for LinkedHashMap<HashedValue, Value> {
    fn get_type() -> &'static str {
        "dict"
    }

    fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item = Value> + 'a> {
        Box::new(
            self.iter()
                .flat_map(|(k, v)| vec![k.get_value().clone(), v.clone()].into_iter()),
        )
    }

    fn to_repr(&self) -> String {
        format!(
            "{{{}}}",
            self.iter()
                .map(|(k, v)| format!("{}: {}", k.get_value().to_repr(), v.to_repr()))
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                })
        )
    }

    fn to_bool(&self) -> bool {
        !self.is_empty()
    }

    fn at(&self, index: Value) -> Result<Value, ValueError> {
        match self.get(&HashedValue::new(index.clone())?) {
            Some(v) => Ok(v.clone()),
            None => Err(ValueError::KeyNotFound(index)),
        }
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.len() as i64)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        Ok(self.contains_key(&HashedValue::new(other.clone())?))
    }

    fn iter(&self) -> Result<Vec<Value>, ValueError> {
        Ok(self.iter().map(|x| x.0.get_value().clone()).collect())
    }

    fn add(&self, other: &Self) -> Result<Self, ValueError> {
        let mut result = LinkedHashMap::new();
        for (k, v) in self.iter() {
            result.insert(k.clone(), v.clone());
        }
        for (k, v) in other.iter() {
            result.insert(k.clone(), v.clone());
        }
        Ok(result)
    }

    fn compare(&self, other: &Self, recursion: u32) -> Result<Ordering, ValueError> {
        let mut v1: Vec<Value> = self.keys().map(|v| v.get_value().clone()).collect();
        let mut v2: Vec<Value> = other.keys().map(|v| v.get_value().clone()).collect();
        // We sort the keys because the dictionary preserve insertion order but ordering does
        // not matter in the comparison. This make the comparison O(n.log n) instead of O(n).
        v1.sort();
        v2.sort();
        let mut iter1 = v1.into_iter();
        let mut iter2 = v2.into_iter();
        loop {
            match (iter1.next(), iter2.next()) {
                (None, None) => return Ok(Ordering::Equal),
                (None, Some(..)) => return Ok(Ordering::Less),
                (Some(..), None) => return Ok(Ordering::Greater),
                (Some(k1), Some(k2)) => {
                    let r = k1.compare(&k2, recursion + 1)?;
                    if r != Ordering::Equal {
                        return Ok(r);
                    }
                    let r = self.at(k1)?.compare(&other.at(k2)?, recursion + 1)?;
                    if r != Ordering::Equal {
                        return Ok(r);
                    }
                }
            }
        }
    }

    not_supported!(slice, mul, get_hash, arithmetic, to_int, pipe, attr, function, percent);
}

impl MutableContent for LinkedHashMap<HashedValue, Value> {
    fn set_at_check(&self, _index: &Value) -> Result<(), ValueError> {
        Ok(())
    }

    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        let index_key = HashedValue::new(index)?;
        {
            if let Some(x) = self.get_mut(&index_key) {
                *x = new_value;
                return Ok(());
            }
        }
        self.insert(index_key, new_value);
        Ok(())
    }

    not_supported!(set_attr);
}

/// The Dictionary type
pub type Dictionary = Mutable<LinkedHashMap<HashedValue, Value>>;

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Eq + Clone> TryFrom<HashMap<T1, T2>>
    for Dictionary
{
    type Error = ValueError;

    fn try_from(a: HashMap<T1, T2>) -> Result<Dictionary, ValueError> {
        let mut result = LinkedHashMap::new();
        for (k, v) in a.iter() {
            result.insert(HashedValue::new(k.clone().into())?, v.clone().into());
        }
        Ok(Dictionary::new(result))
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Eq + Clone>
    TryFrom<LinkedHashMap<T1, T2>> for Dictionary
{
    type Error = ValueError;

    fn try_from(a: LinkedHashMap<T1, T2>) -> Result<Dictionary, ValueError> {
        let mut result = LinkedHashMap::new();
        for (k, v) in a.iter() {
            result.insert(HashedValue::new(k.clone().into())?, v.clone().into());
        }
        Ok(Dictionary::new(result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mutate_dict() {
        let mut map = LinkedHashMap::<HashedValue, Value>::new();
        map.insert(HashedValue::new(Value::from(1)).unwrap(), Value::from(2));
        map.insert(HashedValue::new(Value::from(2)).unwrap(), Value::from(4));
        let mut d = Value::try_from(map).unwrap();
        assert_eq!("{1: 2, 2: 4}", d.to_str());
        d.set_at(Value::from(2), Value::from(3)).unwrap();
        assert_eq!("{1: 2, 2: 3}", d.to_str());
        d.set_at(Value::from((3, 4)), Value::from(5)).unwrap();
        assert_eq!("{1: 2, 2: 3, (3, 4): 5}", d.to_str());
    }

    #[test]
    fn test_is_descendant() {
        let mut map = LinkedHashMap::<HashedValue, Value>::new();
        map.insert(HashedValue::new(Value::from(1)).unwrap(), Value::from(2));
        map.insert(HashedValue::new(Value::from(2)).unwrap(), Value::from(4));
        let v1 = Value::try_from(map.clone()).unwrap();
        map.insert(HashedValue::new(Value::from(3)).unwrap(), v1.clone());
        let v2 = Value::try_from(map.clone()).unwrap();
        map.insert(HashedValue::new(Value::from(3)).unwrap(), v2.clone());
        let v3 = Value::try_from(map).unwrap();
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
