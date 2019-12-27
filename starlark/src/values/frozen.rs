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

//! Frozen value-related utilities.

use crate::values::TypedValue;
use crate::values::Value;

/// Marker trait for types which are frozen on creation.
///
/// All types which are immutable and do not reference other objects
/// are frozen on creation.
///
/// `int`, `NoneType`, `str` are permanently frozen.
///
/// But tuple is not frozen on creation.
pub trait FrozenOnCreation {}

/// [`Value`] wrapper which asserts the value is frozen.
#[derive(Clone, Debug)]
pub(crate) struct FrozenValue(Value);

impl FrozenValue {
    pub fn new(value: Value) -> Result<FrozenValue, ()> {
        if value.is_frozen() {
            Ok(FrozenValue(value))
        } else {
            Err(())
        }
    }
}

impl From<FrozenValue> for Value {
    fn from(v: FrozenValue) -> Self {
        v.0
    }
}

impl<T> From<T> for FrozenValue
where
    T: TypedValue + FrozenOnCreation,
{
    fn from(t: T) -> Self {
        FrozenValue::new(Value::new(t)).unwrap()
    }
}
