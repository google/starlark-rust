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
use linked_hash_map::LinkedHashMap; // To preserve insertion order
use std::borrow::BorrowMut;
use std::cmp::Ordering;
use std::collections::HashMap;
use values::*;

/// The Dictionary type
pub struct Dictionary {
    mutability: IterableMutability,
    content: LinkedHashMap<Value, Value>,
}

impl Dictionary {
    pub fn new() -> Value {
        Value::new(Dictionary {
            mutability: IterableMutability::Mutable,
            content: LinkedHashMap::new(),
        })
    }

    pub fn apply<Return>(v: &Value, f: &Fn(&LinkedHashMap<Value, Value>) -> Result<Return, ValueError>) -> Result<Return, ValueError> {
        if v.get_type() != "dict" {
            Err(ValueError::IncorrectParameterType)
        } else {
            v.downcast_apply(|x: &Dictionary| -> Result<Return, ValueError> { f(&x.content) })
        }
    }

    pub fn mutate(
        v: &Value,
        f: &Fn(&mut LinkedHashMap<Value, Value>) -> ValueResult,
    ) -> ValueResult {
        if v.get_type() != "dict" {
            Err(ValueError::IncorrectParameterType)
        } else {
            let mut v = v.clone();
            v.downcast_apply_mut(|x: &mut Dictionary| -> ValueResult {
                x.mutability.test()?;
                f(&mut x.content)
            })
        }
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Hash + Eq + Clone> From<HashMap<T1, T2>>
    for Dictionary
{
    fn from(a: HashMap<T1, T2>) -> Dictionary {
        let mut result = Dictionary {
            mutability: IterableMutability::Mutable,
            content: LinkedHashMap::new(),
        };
        for (k, v) in a.iter() {
            result.content.insert(k.clone().into(), v.clone().into());
        }
        result
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Hash + Eq + Clone>
    From<LinkedHashMap<T1, T2>> for Dictionary
{
    fn from(a: LinkedHashMap<T1, T2>) -> Dictionary {
        let mut result = Dictionary {
            mutability: IterableMutability::Mutable,
            content: LinkedHashMap::new(),
        };
        for (k, v) in a.iter() {
            result.content.insert(k.clone().into(), v.clone().into());
        }
        result
    }
}

/// Define the Dictionary type
impl TypedValue for Dictionary {
    any!();

    fn freeze(&mut self) {
        self.mutability.freeze();
        for (_, v) in self.content.iter_mut() {
            // XXX: We cannot freeze the key because they are immutable in rust, is it important?
            (*v).borrow_mut().freeze();
        }
    }
    define_iterable_mutability!(mutability);

    fn to_str(&self) -> String {
        format!(
            "{{{}}}",
            self.content
                .iter()
                .map(|(k, v)| format!("{}: {}", k.to_repr(), v.to_repr()))
                .enumerate()
                .fold("".to_string(), |accum, s| if s.0 == 0 {
                    accum + &s.1
                } else {
                    accum + ", " + &s.1
                })
        )
    }

    fn to_repr(&self) -> String {
        self.to_str()
    }

    fn get_type(&self) -> &'static str {
        "dict"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn compare(&self, other: &TypedValue, recursion: u32) -> Result<Ordering, ValueError> {
        if other.get_type() == "dict" {
            let mut v1: Vec<Value> = self.into_iter()?.collect();
            let mut v2: Vec<Value> = other.into_iter()?.collect();
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
                        let r = self
                            .at(k1)?
                            .compare(&other.at(k2).unwrap(), recursion + 1)?;
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
        // Fail the function if the index is non hashable
        index.get_hash()?;
        match self.content.get(&index) {
            Some(v) => Ok(v.clone()),
            None => Err(ValueError::KeyNotFound(index.clone())),
        }
    }

    fn length(&self) -> Result<i64, ValueError> {
        Ok(self.content.len() as i64)
    }

    fn is_in(&self, other: &Value) -> ValueResult {
        // Fail the function if the index is non hashable
        other.get_hash()?;
        Ok(Value::new(self.content.contains_key(other)))
    }

    fn is_descendant(&self, other: &TypedValue) -> bool {
        self.content.iter().any(|(k, v)| {
            k.same_as(other) || v.same_as(other) || k.is_descendant(other) || v.is_descendant(other)
        })
    }

    fn into_iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError> {
        Ok(Box::new(self.content.iter().map(|x| x.0.clone())))
    }

    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        // Fail the function if the index is non hashable
        index.get_hash()?;
        self.mutability.test()?;
        let new_value = new_value.clone_for_container(self)?;
        {
            if let Some(x) = self.content.get_mut(&index) {
                *x = new_value;
                return Ok(());
            }
        }
        self.content.insert(index, new_value);
        Ok(())
    }

    fn add(&self, other: Value) -> ValueResult {
        if other.get_type() == "dict" {
            let mut result = Dictionary {
                mutability: IterableMutability::Mutable,
                content: LinkedHashMap::new(),
            };
            for (k, v) in self.content.iter() {
                result.content.insert(k.clone(), v.clone());
            }
            for k in other.into_iter()? {
                result.content.insert(k.clone(), other.at(k)?.clone());
            }
            Ok(Value::new(result))
        } else {
            Err(ValueError::IncorrectParameterType)
        }
    }

    not_supported!(plus, minus, sub, mul, div, pipe, percent, floor_div);
    not_supported!(to_int, get_hash, slice, attr, function);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mutate_dict() {
        let mut map = LinkedHashMap::<Value, Value>::new();
        map.insert(Value::from(1), Value::from(2));
        map.insert(Value::from(2), Value::from(4));
        let mut d = Value::from(map);
        assert_eq!("{1: 2, 2: 4}", d.to_str());
        d.set_at(Value::from(2), Value::from(3)).unwrap();
        assert_eq!("{1: 2, 2: 3}", d.to_str());
        d.set_at(Value::from((3, 4)), Value::from(5)).unwrap();
        assert_eq!("{1: 2, 2: 3, (3, 4): 5}", d.to_str());
    }

    #[test]
    fn test_is_descendant() {
        let mut map = LinkedHashMap::<Value, Value>::new();
        map.insert(Value::from(1), Value::from(2));
        map.insert(Value::from(2), Value::from(4));
        let v1 = Value::from(map.clone());
        map.insert(Value::from(3), v1.clone());
        let v2 = Value::from(map.clone());
        map.insert(Value::from(3), v2.clone());
        let v3 = Value::from(map);
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
