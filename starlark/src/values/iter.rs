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

//! Iterable for Starlark objects.

use crate::values::mutability::RefOrRef;
use crate::values::Value;

/// Type to be implemented by types which are iterable.
pub trait TypedIterable: 'static {
    /// Make an iterator.
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a>;

    /// Specialized faster version of iteration when results as vec is needed
    fn to_vec(&self) -> Vec<Value> {
        self.to_iter().into_iter().collect()
    }
}

/// Iterable which contains borrowed reference to a sequence.
pub struct RefIterable<'a> {
    r: RefOrRef<'a, dyn TypedIterable>,
}

impl<'a> RefIterable<'a> {
    pub fn new(r: RefOrRef<'a, dyn TypedIterable>) -> RefIterable<'a> {
        RefIterable { r }
    }

    pub fn iter(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        self.r.to_iter()
    }

    pub fn to_vec(&self) -> Vec<Value> {
        self.r.to_vec()
    }
}

impl<'a> IntoIterator for &'a RefIterable<'a> {
    type Item = Value;
    type IntoIter = Box<dyn Iterator<Item = Value> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Fake iterable needed to be able to do `Ref::map` with error.
pub(crate) struct FakeTypedIterable;

impl TypedIterable for FakeTypedIterable {
    fn to_iter<'a>(&'a self) -> Box<dyn Iterator<Item = Value> + 'a> {
        unreachable!()
    }
}
