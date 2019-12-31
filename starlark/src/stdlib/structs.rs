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

use crate::values::error::ValueError;
use crate::values::string::rc::RcString;
use crate::values::*;
use linked_hash_map::LinkedHashMap;
use std::fmt;
use std::fmt::Write as _;

/// `struct()` implementation.
pub struct StarlarkStruct {
    fields: LinkedHashMap<RcString, Value>,
}

impl StarlarkStruct {
    pub(crate) fn new(fields: LinkedHashMap<RcString, Value>) -> StarlarkStruct {
        StarlarkStruct { fields }
    }
}

impl TypedValue for StarlarkStruct {
    type Holder = Immutable<StarlarkStruct>;

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(self.fields.values().cloned())
    }

    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        write!(buf, "struct(")?;
        for (i, (name, value)) in self.fields.iter().enumerate() {
            if i != 0 {
                write!(buf, ", ")?;
            }
            write!(buf, "{}=", name)?;
            value.to_repr_impl(buf)?;
        }
        write!(buf, ")")?;
        Ok(())
    }

    const TYPE: &'static str = "struct";

    fn equals(&self, other: &StarlarkStruct) -> Result<bool, ValueError> {
        if self.fields.len() != other.fields.len() {
            return Ok(false);
        }

        for (field, a) in &self.fields {
            match other.fields.get(field) {
                None => return Ok(false),
                Some(b) => {
                    if !a.equals(b)? {
                        return Ok(false);
                    }
                }
            }
        }

        Ok(true)
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

    fn dir_attr(&self) -> Result<Vec<RcString>, ValueError> {
        Ok(self.fields.keys().cloned().collect())
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
        Ok(Value::new(StarlarkStruct::new(kwargs)))
    }
}
