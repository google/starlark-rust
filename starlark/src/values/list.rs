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
use crate::stdlib::list::LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE;
use crate::values::error::{RuntimeError, ValueError};
use crate::values::iter::TypedIterable;
use crate::values::*;
use std::cmp::Ordering;
use std::fmt;

#[derive(Clone, Default)]
pub struct List {
    content: Vec<Value>,
}

impl<T: Into<Value>> From<Vec<T>> for List {
    fn from(a: Vec<T>) -> List {
        List {
            content: a.into_iter().map(Into::into).collect(),
        }
    }
}

impl<T: Into<Value>> From<Vec<T>> for Value {
    fn from(a: Vec<T>) -> Value {
        Value::new(List::from(a))
    }
}

impl List {
    pub fn new() -> Value {
        Value::new(List {
            content: Vec::new(),
        })
    }

    pub fn push(&mut self, value: Value) {
        self.content.push(value);
    }

    pub fn extend(&mut self, other: Value) -> Result<(), ValueError> {
        let other: Vec<Value> = other.iter()?.iter().collect();
        self.content.extend(other);
        Ok(())
    }

    pub fn clear(&mut self) {
        self.content.clear();
    }

    pub fn insert(&mut self, index: usize, value: Value) -> Result<(), ValueError> {
        self.content.insert(index, value);
        Ok(())
    }

    pub fn pop(&mut self, index: i64) -> Result<Value, ValueError> {
        if index < 0 || index >= self.content.len() as i64 {
            return Err(ValueError::IndexOutOfBound(index));
        }
        Ok(self.content.remove(index as usize))
    }

    pub fn remove(&mut self, needle: Value) -> Result<(), ValueError> {
        let position = match self.content.iter().position(|v| v == &needle) {
            Some(position) => position,
            None => {
                return Err(RuntimeError {
                    code: LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE,
                    message: format!("Element '{}' not found in '{}'", needle, self.to_str()),
                    label: "not found".to_owned(),
                }
                .into());
            }
        };
        self.content.remove(position);
        Ok(())
    }

    pub fn remove_at(&mut self, index: usize) -> Value {
        self.content.remove(index)
    }
}

impl TypedValue for List {
    type Holder = Mutable<List>;

    fn gc(&mut self) {
        self.content.clear();
    }

    fn visit_links(&self, visitor: &mut dyn FnMut(&Value)) {
        for v in &self.content {
            visitor(v);
        }
    }

    /// Returns a string representation for the list
    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        write!(buf, "[")?;
        for (i, v) in self.content.iter().enumerate() {
            if i != 0 {
                write!(buf, ", ")?;
            }
            v.to_repr_impl(buf)?;
        }
        write!(buf, "]")?;
        Ok(())
    }

    const TYPE: &'static str = "list";
    fn to_bool(&self) -> bool {
        !self.content.is_empty()
    }

    fn equals(&self, other: &List) -> Result<bool, ValueError> {
        if self.content.len() != other.content.len() {
            return Ok(false);
        }

        let mut self_iter = self.content.iter();
        let mut other_iter = other.content.iter();

        loop {
            match (self_iter.next(), other_iter.next()) {
                (Some(a), Some(b)) => {
                    if !a.equals(b)? {
                        return Ok(false);
                    }
                }
                (None, None) => {
                    return Ok(true);
                }
                _ => unreachable!(),
            }
        }
    }

    fn compare(&self, other: &List) -> Result<Ordering, ValueError> {
        let mut iter1 = self.content.iter();
        let mut iter2 = other.content.iter();
        loop {
            match (iter1.next(), iter2.next()) {
                (None, None) => return Ok(Ordering::Equal),
                (None, Some(..)) => return Ok(Ordering::Less),
                (Some(..), None) => return Ok(Ordering::Greater),
                (Some(v1), Some(v2)) => {
                    let r = v1.compare(&v2)?;
                    if r != Ordering::Equal {
                        return Ok(r);
                    }
                }
            }
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
            if x.equals(other)? {
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
            self.content.iter(),
        )))
    }

    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    /// Concatenate `other` to the current value.
    fn add(&self, other: &List) -> Result<List, ValueError> {
        let mut result = List {
            content: Vec::new(),
        };
        for x in &self.content {
            result.content.push(x.clone());
        }
        for x in &other.content {
            result.content.push(x.clone());
        }
        Ok(result)
    }

    /// Repeat `other` times this tuple.
    fn mul(&self, other: Value) -> ValueResult {
        match other.downcast_ref::<i64>() {
            Some(l) => {
                let mut result = List {
                    content: Vec::new(),
                };
                for _i in 0..*l {
                    result.content.extend(self.content.iter().cloned());
                }
                Ok(Value::new(result))
            }
            None => Err(ValueError::IncorrectParameterType),
        }
    }

    /// Set the value at `index` to `new_value`
    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        let i = index.convert_index(self.length()?)? as usize;
        self.content[i] = new_value;
        Ok(())
    }
}

impl TypedIterable for List {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.content.iter().cloned())
    }

    fn to_vec(&self) -> Vec<Value> {
        self.content.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::environment::Environment;
    use crate::gc;

    #[test]
    fn test_to_str() {
        let env = Environment::new("test");
        let _g = gc::push_env(&env);

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
        let env = Environment::new("test");
        let _g = gc::push_env(&env);

        let mut v = Value::from(vec![1, 2, 3]);
        v.set_at(Value::from(1), Value::from(1)).unwrap();
        v.set_at(Value::from(2), Value::from(vec![2, 3])).unwrap();
        assert_eq!(&v.to_repr(), "[1, 1, [2, 3]]");
    }

    #[test]
    fn test_arithmetic_on_list() {
        let env = Environment::new("test");
        let _g = gc::push_env(&env);

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
        let env = Environment::new("test");
        let _g = gc::push_env(&env);

        let v1 = Value::from(vec![1, 2, 3]);
        let mut v2 = v1.clone();
        v2.set_at(Value::from(2), Value::from(4)).unwrap();
        assert_eq!(v2.to_str(), "[1, 2, 4]");
        assert_eq!(v1.to_str(), "[1, 2, 4]");
    }
}
