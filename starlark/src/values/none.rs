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

//! Define the None type for Starlark.

use crate::values::error::ValueError;
use crate::values::*;
use std::cmp::Ordering;
use std::fmt;

/// Define the NoneType type
#[derive(Debug, Clone, Copy)]
pub enum NoneType {
    None,
}

/// Define the NoneType type
impl TypedValue for NoneType {
    type Holder = ImmutableNoValues<Self>;
    const TYPE: &'static str = "NoneType";

    fn new_value(self) -> Value {
        Value(ValueInner::None(self))
    }

    fn equals(&self, _other: &NoneType) -> Result<bool, ValueError> {
        Ok(true)
    }
    fn compare(&self, _other: &NoneType) -> Result<Ordering, ValueError> {
        Ok(Ordering::Equal)
    }

    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        write!(buf, "None")
    }
    fn to_bool(&self) -> bool {
        false
    }
    // just took the result of hash(None) in macos python 2.7.10 interpreter.
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(9_223_380_832_852_120_682)
    }
}

impl From<NoneType> for Value {
    fn from(NoneType::None: NoneType) -> Self {
        Value::new(NoneType::None)
    }
}
