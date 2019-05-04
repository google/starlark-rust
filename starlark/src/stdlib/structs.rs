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

//! Implementation of `struct` function.

use crate::values::immutable::{ImmutableContent, ReadableContent};
use crate::values::*;
use linked_hash_map::LinkedHashMap;
use std::cmp::Ordering;

/// `struct()` implementation.
pub struct StarlarkStruct {
    fields: LinkedHashMap<String, Value>,
}

impl ImmutableContent for StarlarkStruct {}

impl ReadableContent for StarlarkStruct {
    fn to_str(&self) -> String {
        self.to_repr()
    }

    fn to_repr(&self) -> String {
        let mut r = "struct(".to_owned();
        for (i, (name, value)) in self.fields.iter().enumerate() {
            if i != 0 {
                r.push_str(", ");
            }
            r.push_str(&name);
            r.push_str("=");
            r.push_str(&value.to_repr());
        }
        r.push_str(")");
        r
    }

    fn get_type() -> &'static str {
        "struct"
    }

    fn to_bool(&self) -> bool {
        true
    }

    fn get_attr(&self, attribute: &str) -> Result<Value, ValueError> {
        match self.fields.get(attribute) {
            Some(v) => Ok(v.clone()),
            None => Err(ValueError::OperationNotSupported {
                op: attribute.to_owned(),
                left: self.to_repr(),
                right: None,
            }),
        }
    }

    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        Ok(self.fields.contains_key(attribute))
    }

    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        Ok(self.fields.keys().cloned().collect())
    }

    fn compare(&self, other: &StarlarkStruct, recursion: u32) -> Result<Ordering, ValueError> {
        let mut self_keys: Vec<_> = self.fields.keys().collect();
        let mut other_keys: Vec<_> = other.fields.keys().collect();
        self_keys.sort();
        other_keys.sort();
        let mut self_keys = self_keys.into_iter();
        let mut other_keys = other_keys.into_iter();
        loop {
            match (self_keys.next(), other_keys.next()) {
                (None, None) => return Ok(Ordering::Equal),
                (None, Some(_)) => return Ok(Ordering::Less),
                (Some(_), None) => return Ok(Ordering::Greater),
                (Some(s_k), Some(o_k)) => {
                    let s_v = self.fields.get(s_k).unwrap();
                    let o_v = other.fields.get(o_k).unwrap();
                    match s_v.compare(o_v, recursion + 1)? {
                        Ordering::Equal => continue,
                        ordering => return Ok(ordering),
                    }
                }
            }
        }
    }

    not_supported!(binop);
    not_supported!(is_in, call);
    not_supported!(iter, length, slice, at, get_hash, to_int);

    fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item = Value> + 'a> {
        Box::new(self.fields.values().cloned())
    }
}

starlark_module! { global =>
    /// Creates a struct.
    ///
    /// `struct` creates a struct. It accepts keyword arguments, keys become struct field names,
    /// and values become field values.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("(
    /// struct(host='localhost', port=80).port == 80
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dir(struct(host='localhost', port=80)) == ['host', 'port']
    /// # )").unwrap());
    /// # assert!(starlark_default("(
    /// dir(struct()) == []
    /// # )").unwrap());
    /// ```
    struct_(**kwargs) {
        Ok(Value::new_imm(StarlarkStruct {
            fields: kwargs
        }))
    }
}
