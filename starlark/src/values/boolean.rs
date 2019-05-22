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

//! Define the bool type for Starlark.

use crate::values::error::ValueError;
use crate::values::*;
use std::cmp::Ordering;

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Value::new(b)
    }
}

/// Define the bool type
impl TypedValue for bool {
    immutable!();
    any!();
    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        Ok(*self == *other.downcast_ref::<bool>().unwrap())
    }
    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        Ok(self.cmp(&*other.downcast_ref::<bool>().unwrap()))
    }
    fn to_repr(&self) -> String {
        if *self {
            "True".to_owned()
        } else {
            "False".to_owned()
        }
    }
    fn to_int(&self) -> Result<i64, ValueError> {
        Ok(if *self { 1 } else { 0 })
    }
    fn get_type(&self) -> &'static str {
        "bool"
    }
    fn to_bool(&self) -> bool {
        *self
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(self.to_int().unwrap() as u64)
    }
    fn is_descendant(&self, _other: &TypedValue) -> bool {
        false
    }
}
