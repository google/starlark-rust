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

use crate::values::*;

/// Define the NoneType type
impl TypedValue for Option<()> {
    immutable!();
    any!();
    default_compare!();
    fn to_repr(&self) -> String {
        "None".to_owned()
    }
    fn get_type(&self) -> &'static str {
        "NoneType"
    }
    fn to_bool(&self) -> bool {
        false
    }
    // just took the result of hash(None) in macos python 2.7.10 interpreter.
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(9_223_380_832_852_120_682)
    }
    fn is_descendant(&self, _other: &TypedValue) -> bool {
        false
    }
}

impl From<Option<()>> for Value {
    fn from(_a: Option<()>) -> Value {
        Value::new(None)
    }
}
