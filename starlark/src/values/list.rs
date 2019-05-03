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
use crate::values::*;
use std::borrow::BorrowMut;
use std::cmp::Ordering;

pub struct List {
    mutability: IterableMutability,
    content: Vec<Value>,
}

impl<T: Into<Value> + Clone> From<Vec<T>> for List {
    fn from(a: Vec<T>) -> List {
        let mut result = List {
            mutability: IterableMutability::Mutable,
            content: Vec::new(),
        };
        for x in a.iter() {
            let v: Value = x.clone().into();
            result.content.push(v);
        }
        result
    }
}

impl List {
    #[allow(clippy::new_ret_no_self)]
    pub fn new() -> Value {
        Value::new(List {
            mutability: IterableMutability::Mutable,
            content: Vec::new(),
        })
    }

    pub fn mutate(v: &Value, f: &dyn Fn(&mut Vec<Value>) -> ValueResult) -> ValueResult {
        let mut v = v.clone();
        v.downcast_apply_mut(|x: &mut List| -> ValueResult {
            x.mutability.test()?;
            f(&mut x.content)
        })
        .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl TypedValue for List {
    any!();

    define_iterable_mutability!(mutability);

    fn freeze(&mut self) {
        self.mutability.freeze();
        for x in self.content.iter_mut() {
            x.borrow_mut().freeze();
        }
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
    fn to_str(&self) -> String {
        format!(
            "[{}]",
            self.content
                .iter()
                .map(Value::to_repr)
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
        "list"
    }
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn compare(&self, other: &dyn TypedValue, recursion: u32) -> Result<Ordering, ValueError> {
        if other.get_type() == "list" {
            let mut iter1 = self.iter()?;
            let mut iter2 = other.iter()?;
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

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        for x in self.content.iter() {
            if x.compare(other, 0)? == Ordering::Equal {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn is_descendant(&self, other: &dyn TypedValue) -> bool {
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
        Ok(Value::from(tuple::slice_vector(
            start,
            stop,
            stride,
            self.content.iter(),
        )))
    }

    fn iter<'a>(&'a self) -> Result<Box<dyn Iterator<Item = Value> + 'a>, ValueError> {
        Ok(Box::new(self.content.iter().cloned()))
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
    fn add(&self, other: Value) -> ValueResult {
        if other.get_type() == "list" {
            let mut result = List {
                mutability: IterableMutability::Mutable,
                content: Vec::new(),
            };
            for x in self.content.iter() {
                result.content.push(x.clone());
            }
            for x in other.iter()? {
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
            let mut result = List {
                mutability: IterableMutability::Mutable,
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
        self.mutability.test()?;
        let i = index.convert_index(self.length()?)? as usize;
        self.content[i] = new_value.clone_for_container(self)?;
        Ok(())
    }

    not_supported!(attr, function, get_hash);
    not_supported!(plus, minus, sub, div, pipe, percent, floor_div);
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
        let v2 = Value::from(vec![Value::new(1), Value::new(2), v1.clone()]);
        let v3 = Value::from(vec![Value::new(1), Value::new(2), v2.clone()]);
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
