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

//! Error-safe value and hash pair.

use crate::values::{Value, ValueError};
use core::borrow::BorrowMut;
use std::hash::{Hash, Hasher};

/// A pair of value and cached value hash.
///
/// This struct contains both value and a precomputed hash of that value.
/// If a value is not hashable, this error is raised at `DictionaryKey` construction.
/// So the implementation of `Hash` for this struct does not need to handle `hash` errors.
#[derive(Eq, Clone)]
pub struct HashedValue {
    hash: u64,
    value: Value,
}

impl From<HashedValue> for Value {
    fn from(key: HashedValue) -> Value {
        key.value
    }
}

impl HashedValue {
    /// Returns error if the value is non hashable.
    pub fn new(value: Value) -> Result<HashedValue, ValueError> {
        let hash = value.get_hash()?;
        Ok(HashedValue { hash, value })
    }

    /// Get precomputed hash.
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    /// Get contained value.
    pub fn get_value(&self) -> &Value {
        &self.value
    }

    /// Freeze the value, should be no-op since only immutable values can be hashed.
    pub fn freeze(&mut self) {
        self.value.borrow_mut().freeze();
    }
}

impl PartialEq for HashedValue {
    fn eq(&self, other: &HashedValue) -> bool {
        self.hash == other.hash && self.value == other.value
    }
}

impl Hash for HashedValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.hash)
    }
}
