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
use values::*;
use std::collections::HashMap;
use linked_hash_map::LinkedHashMap; // To preserve insertion order
use std::cmp::Ordering;
use std::borrow::BorrowMut;

/// The Dictionary type
pub struct Dictionary {
    frozen: bool,
    content: LinkedHashMap<Value, Value>,
}

impl Dictionary {
    pub fn new() -> Value {
        Value::new(Dictionary {
            frozen: false,
            content: LinkedHashMap::new(),
        })
    }

    pub fn apply(
        v: &Value,
        f: &Fn(&LinkedHashMap<Value, Value>) -> ValueResult
    ) -> ValueResult {
        if v.get_type() != "dict" {
            Err(ValueError::IncorrectParameterType)
        } else {
            let mut v = v.clone();
            v.downcast_apply(|x: &mut Dictionary| -> ValueResult {
                f(&x.content)
            })
        }
    }

    pub fn mutate(
        v: &Value,
        f: &Fn(&mut LinkedHashMap<Value, Value>) -> ValueResult
    ) -> ValueResult {
        if v.get_type() != "dict" {
            Err(ValueError::IncorrectParameterType)
        } else {
            let mut v = v.clone();
            v.downcast_apply(|x: &mut Dictionary| -> ValueResult {
                if x.frozen {
                    Err(ValueError::CannotMutateImmutableValue)
                } else {
                    f(&mut x.content)
                }
            })
        }
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Hash + Eq + Clone> From<HashMap<T1, T2>>
    for Dictionary {
    fn from(a: HashMap<T1, T2>) -> Dictionary {
        let mut result = Dictionary {
            frozen: false,
            content: LinkedHashMap::new(),
        };
        for (k, v) in a.iter() {
            result.content.insert(k.clone().into(), v.clone().into());
        }
        result
    }
}

impl<T1: Into<Value> + Hash + Eq + Clone, T2: Into<Value> + Hash + Eq + Clone> From<LinkedHashMap<T1, T2>>
    for Dictionary {
    fn from(a: LinkedHashMap<T1, T2>) -> Dictionary {
        let mut result = Dictionary {
            frozen: false,
            content: LinkedHashMap::new(),
        };
        for (k, v) in a.iter() {
            result.content.insert(k.clone().into(), v.clone().into());
        }
        result
    }
}

/// Define the tuple type
impl TypedValue for Dictionary {
    any!();

    fn immutable(&self) -> bool {
        self.frozen
    }
    fn freeze(&mut self) {
        self.frozen = true;
        for (_, v) in self.content.iter_mut() {
            // XXX: We cannot freeze the key because they are immutable in rust, is it important?
            (*v).borrow_mut().freeze();
        }
    }

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

    fn compare(&self, other: Value) -> Ordering {
        if other.get_type() == "tuple" {
            let mut iter1 = self.into_iter().unwrap();
            let mut iter2 = other.into_iter().unwrap();
            loop {
                match (iter1.next(), iter2.next()) {
                    (None, None) => return Ordering::Equal,
                    (None, Some(..)) => return Ordering::Less,
                    (Some(..), None) => return Ordering::Greater,
                    (Some(v1), Some(v2)) => {
                        let r = v1.compare(v2);
                        if r != Ordering::Equal {
                            return r;
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

    fn is_in(&self, other: Value) -> ValueResult {
        // Fail the function if the index is non hashable
        other.get_hash()?;
        Ok(Value::new(self.content.contains_key(&other)))
    }

    fn into_iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError> {
        Ok(Box::new(self.content.iter().map(|x| x.0.clone())))
    }

    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        // Fail the function if the index is non hashable
        index.get_hash()?;
        if self.frozen {
            Err(ValueError::CannotMutateImmutableValue)
        } else {
            self.content.insert(index, new_value);
            Ok(())
        }
    }

    not_supported!(to_int, get_hash, slice, attr, function, binop);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mutate_dict() {
        let mut map = HashMap::<Value, Value>::new();
        map.insert(Value::from(1), Value::from(2));
        map.insert(Value::from(2), Value::from(4));
        let mut d = Value::from(map);
        d.set_at(Value::from(2), Value::from(3)).unwrap();
        assert_eq!("{1: 2, 2: 3}", d.to_str());
        d.set_at(Value::from((3, 4)), Value::from(5)).unwrap();
        assert_eq!("{1: 2, 2: 3, (3, 4): 5}", d.to_str());
    }
}
