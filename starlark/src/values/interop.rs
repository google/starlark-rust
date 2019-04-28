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

//! Utilities for easier interop with Rust.

use std::convert::TryFrom;

use crate::values::dict::Dictionary;
use crate::values::{TypedValue, Value, ValueError};
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash};

/// Type convertible from Starlark value.
pub trait StarlarkParameterToRust: Sized {
    /// Convert a value from Starlark
    fn from_starlark(value: Value) -> Result<Self, ValueError>;
}

impl StarlarkParameterToRust for Value {
    fn from_starlark(value: Value) -> Result<Self, ValueError> {
        Ok(value)
    }
}

impl StarlarkParameterToRust for String {
    fn from_starlark(value: Value) -> Result<String, ValueError> {
        value
            .downcast_apply(String::clone)
            .ok_or(ValueError::IncorrectParameterType)
    }
}

impl StarlarkParameterToRust for bool {
    fn from_starlark(value: Value) -> Result<bool, ValueError> {
        value
            .downcast_apply(|i: &bool| *i)
            .ok_or(ValueError::IncorrectParameterType)
    }
}

impl StarlarkParameterToRust for i64 {
    fn from_starlark(value: Value) -> Result<i64, ValueError> {
        value
            .downcast_apply(|i: &i64| *i)
            .ok_or(ValueError::IncorrectParameterType)
    }
}

impl StarlarkParameterToRust for u64 {
    fn from_starlark(value: Value) -> Result<u64, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                u64::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for u32 {
    fn from_starlark(value: Value) -> Result<u32, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                u32::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for i32 {
    fn from_starlark(value: Value) -> Result<i32, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                i32::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for u16 {
    fn from_starlark(value: Value) -> Result<u16, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                u16::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for i16 {
    fn from_starlark(value: Value) -> Result<i16, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                i16::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for u8 {
    fn from_starlark(value: Value) -> Result<u8, ValueError> {
        value
            .downcast_apply(|i: &i64| u8::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i)))
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for i8 {
    fn from_starlark(value: Value) -> Result<i8, ValueError> {
        value
            .downcast_apply(|i: &i64| i8::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i)))
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for usize {
    fn from_starlark(value: Value) -> Result<usize, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                usize::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl StarlarkParameterToRust for isize {
    fn from_starlark(value: Value) -> Result<isize, ValueError> {
        value
            .downcast_apply(|i: &i64| {
                isize::try_from(*i).map_err(|_| ValueError::IndexOutOfBound(*i))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

impl<T: StarlarkParameterToRust> StarlarkParameterToRust for Vec<T> {
    fn from_starlark(value: Value) -> Result<Self, ValueError> {
        let mut r = Vec::new();
        // Any iterable can be converted to Vec
        for item in value.iter()? {
            r.push(T::from_starlark(item)?);
        }
        Ok(r)
    }
}

impl<K, V, S> StarlarkParameterToRust for HashMap<K, V, S>
where
    K: StarlarkParameterToRust + Eq + Hash,
    V: StarlarkParameterToRust,
    S: BuildHasher + Default,
{
    fn from_starlark(value: Value) -> Result<Self, ValueError> {
        value
            .downcast_apply(|dict: &Dictionary| {
                let mut r = HashMap::default();
                for key in dict.iter()? {
                    let entry_value = value.at(key.clone())?;
                    r.insert(K::from_starlark(key)?, V::from_starlark(entry_value)?);
                }
                Ok(r)
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::values::list::List;
    use std::iter::FromIterator;

    #[test]
    fn from_starlark_basic() {
        assert_eq!(Ok(17usize), usize::from_starlark(Value::new(17i64)));

        let result = u8::from_starlark(Value::new(300));
        if let Err(ValueError::IndexOutOfBound(300)) = result {
            // OK
        } else {
            panic!("{:?}", result);
        }

        let result = u8::from_starlark(Value::new("ab".to_owned()));
        if let Err(ValueError::IncorrectParameterType) = result {
            // OK
        } else {
            panic!("{:?}", result);
        }
    }

    #[test]
    fn from_starlark_list() {
        let list = List::new();
        List::mutate(&list, &|vec| {
            vec.push(Value::new(12i64));
            vec.push(Value::new(13i64));
            Ok(Value::new(Some(())))
        })
        .unwrap();
        assert_eq!(Ok(vec![12, 13]), Vec::<u32>::from_starlark(list));
    }

    #[test]
    fn from_starlark_dict() {
        let dict = Dictionary::new();
        Dictionary::mutate(&dict, &|dict| {
            dict.insert(Value::new(10i64), Value::new(true));
            dict.insert(Value::new(12i64), Value::new(false));
            Ok(Value::new(Some(())))
        })
        .unwrap();
        assert_eq!(
            Ok(HashMap::from_iter(vec![(10, true), (12, false)])),
            HashMap::<u32, bool>::from_starlark(dict)
        );
    }
}
