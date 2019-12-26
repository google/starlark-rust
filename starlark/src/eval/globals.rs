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

//! Utilities to work with scope global variables.

use std::collections::HashMap;

#[derive(Default, Debug, Clone)]
pub(crate) struct Globals {
    name_to_index: HashMap<String, usize>,
}

impl Globals {
    pub fn register_global(&mut self, name: &str) -> usize {
        let global_count = self.name_to_index.len();
        *self
            .name_to_index
            .entry(name.to_owned())
            .or_insert(global_count)
    }

    /// Return the number of global variable slots
    pub fn len(&self) -> usize {
        self.name_to_index.len()
    }
}
