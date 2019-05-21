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

//! Simple implementation of `LinkedHashSet`.

use linked_hash_map::{Entry, LinkedHashMap};
use std::hash::Hash;

/// `LinkedHashSet` is a tiny wrapper around `LinkedHashMap`.
///
/// Using `LinkedHashMap` directly to avoid adding extra dependency.
#[derive(PartialEq, Eq, Debug, Clone, Default)]
pub(crate) struct LinkedHashSet<K: Eq + Hash> {
    map: LinkedHashMap<K, ()>,
}

impl<K: Eq + Hash> LinkedHashSet<K> {
    pub fn new() -> Self {
        LinkedHashSet {
            map: LinkedHashMap::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        LinkedHashSet {
            map: LinkedHashMap::with_capacity(capacity),
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn clear(&mut self) {
        self.map.clear()
    }

    pub fn iter(&self) -> impl Iterator<Item = &K> {
        self.map.keys()
    }

    pub fn contains(&self, value: &K) -> bool {
        self.map.get(value).is_some()
    }

    pub fn insert(&mut self, value: K) {
        self.map.insert(value, ());
    }

    pub fn insert_if_absent(&mut self, value: K) {
        if let Entry::Vacant(e) = self.map.entry(value) {
            e.insert(());
        }
    }

    pub fn remove(&mut self, value: &K) -> bool {
        self.map.remove(value).is_some()
    }

    /// Items in both sets
    pub fn intersection<'a>(&'a self, other: &'a LinkedHashSet<K>) -> impl Iterator<Item = &'a K> {
        let (a, b) = if self.len() <= other.len() {
            (self, other)
        } else {
            (other, self)
        };
        a.iter().filter(move |k| b.contains(k))
    }

    /// Items which are in `self`, but not in `other`.
    pub fn difference<'a>(&'a self, other: &'a LinkedHashSet<K>) -> impl Iterator<Item = &'a K> {
        self.iter().filter(move |k| !other.contains(k))
    }

    /// Items which are in `self` or in `other` but not in `both`
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a LinkedHashSet<K>,
    ) -> impl Iterator<Item = &'a K> {
        self.difference(other).chain(other.difference(self))
    }

    pub fn is_subset(&self, other: &LinkedHashSet<K>) -> bool {
        self.len() <= other.len() && self.iter().all(|k| other.contains(k))
    }

    pub fn pop_front(&mut self) -> Option<K> {
        self.map.pop_front().map(|(k, ())| k)
    }

    pub fn pop_back(&mut self) -> Option<K> {
        self.map.pop_back().map(|(k, ())| k)
    }
}

impl<'a, K: Hash + Eq> IntoIterator for &'a LinkedHashSet<K> {
    type Item = &'a K;
    type IntoIter = linked_hash_map::Keys<'a, K, ()>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.keys()
    }
}
