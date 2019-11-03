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

//! Implementation of various extensions.

use crate::values::none::NoneType;
use crate::values::Value;

starlark_module! { global =>
    /// Freeze a value.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # starlark_default("
    /// a = []
    /// freeze(a)
    /// # ").unwrap();
    /// ```
    freeze(value, /) {
        value.freeze();
        Ok(Value::new(NoneType::None))
    }
}
