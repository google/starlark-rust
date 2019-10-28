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

//! Mutability-related utilities.

use crate::values::ValueError;
use std::cell::{BorrowError, Cell, Ref, RefCell, RefMut};
use std::fmt;
use std::ops::Deref;
use std::usize;

/// A helper enum for defining the level of mutability of an iterable.
#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum IterableMutability {
    Mutable,
    Immutable,
    FrozenForIteration,
}

impl IterableMutability {
    /// Tests the mutability value and return the appropriate error
    ///
    /// This method is to be called simply `mutability.test()?` to return
    /// an error if the current container is no longer mutable.
    pub fn test(self) -> Result<(), ValueError> {
        match self {
            IterableMutability::Mutable => Ok(()),
            IterableMutability::Immutable => Err(ValueError::CannotMutateImmutableValue),
            IterableMutability::FrozenForIteration => Err(ValueError::MutationDuringIteration),
        }
    }
}

/// `std::cell::Ref<T>` or `&T`
pub enum RefOrRef<'a, T: ?Sized + 'a> {
    Ptr(&'a T),
    Borrowed(Ref<'a, T>),
}

impl<'a, T: ?Sized + 'a> Deref for RefOrRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match self {
            RefOrRef::Ptr(p) => p,
            RefOrRef::Borrowed(p) => p.deref(),
        }
    }
}

impl<'a, T: ?Sized + 'a> RefOrRef<'a, T> {
    pub fn map<U: ?Sized, F>(orig: RefOrRef<'a, T>, f: F) -> RefOrRef<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        match orig {
            RefOrRef::Ptr(p) => RefOrRef::Ptr(f(p)),
            RefOrRef::Borrowed(p) => RefOrRef::Borrowed(Ref::map(p, f)),
        }
    }
}

/// Container for data which is either `RefCell` or immutable data.
pub trait RefCellOrImmutable {
    type Content;

    fn new(value: Self::Content) -> Self;
    fn borrow(&self) -> RefOrRef<'_, Self::Content>;
    fn try_borrow(&self) -> Result<RefOrRef<Self::Content>, BorrowError>;
    fn borrow_mut(&self) -> RefMut<'_, Self::Content>;
    fn as_ptr(&self) -> *const Self::Content;
}

/// Container for immutable data
#[derive(Debug, Clone)]
pub struct ImmutableCell<T>(T);

impl<T> RefCellOrImmutable for RefCell<T> {
    type Content = T;

    fn new(value: T) -> Self {
        RefCell::new(value)
    }

    fn borrow(&self) -> RefOrRef<T> {
        RefOrRef::Borrowed(RefCell::borrow(self))
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        RefCell::try_borrow(self).map(RefOrRef::Borrowed)
    }

    fn borrow_mut(&self) -> RefMut<Self::Content> {
        RefCell::borrow_mut(self)
    }

    fn as_ptr(&self) -> *const T {
        RefCell::as_ptr(self)
    }
}

impl<T> RefCellOrImmutable for ImmutableCell<T> {
    type Content = T;

    fn new(value: T) -> Self {
        ImmutableCell(value)
    }

    fn borrow(&self) -> RefOrRef<T> {
        RefOrRef::Ptr(&self.0)
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        Ok(RefOrRef::Ptr(&self.0))
    }

    fn borrow_mut(&self) -> RefMut<Self::Content> {
        panic!("immutable value cannot be mutably borrowed")
    }

    fn as_ptr(&self) -> *const T {
        &self.0 as *const T
    }
}

/// Holder for mutability flag, either cell or always immutable.
pub trait MutabilityCell: fmt::Debug {
    fn get(&self) -> IterableMutability;
    fn freeze(&self);
    fn freeze_for_iteration(&self);
    fn unfreeze_for_iteration(&self);
    fn new() -> Self;
}

#[derive(Debug, Clone)]
pub struct ImmutableMutability;
#[derive(Debug)]
pub struct MutableMutability(Cell<usize>);

impl MutabilityCell for ImmutableMutability {
    fn get(&self) -> IterableMutability {
        IterableMutability::Immutable
    }

    fn freeze(&self) {}

    fn freeze_for_iteration(&self) {}

    fn unfreeze_for_iteration(&self) {}

    /// Create a new cell, initialized to mutable for mutable types,
    /// and immutable for immutable types.
    fn new() -> Self {
        ImmutableMutability
    }
}

/// Mutable object state
#[derive(Copy, Clone)]
enum MutableStateDecoded {
    /// Completely frozen
    Frozen,
    /// Iterator freeze depth, 0 means object is mutable
    IteratorDepth(usize),
}

impl MutableStateDecoded {
    fn encode(&self) -> usize {
        match self {
            MutableStateDecoded::Frozen => usize::max_value(),
            MutableStateDecoded::IteratorDepth(depth) => {
                assert!(*depth != usize::max_value());
                *depth
            }
        }
    }

    fn decode(state: usize) -> MutableStateDecoded {
        if state == usize::max_value() {
            MutableStateDecoded::Frozen
        } else {
            MutableStateDecoded::IteratorDepth(state)
        }
    }
}

impl MutabilityCell for MutableMutability {
    fn get(&self) -> IterableMutability {
        match MutableStateDecoded::decode(self.0.get()) {
            MutableStateDecoded::Frozen => IterableMutability::Immutable,
            MutableStateDecoded::IteratorDepth(0) => IterableMutability::Mutable,
            MutableStateDecoded::IteratorDepth(_) => IterableMutability::FrozenForIteration,
        }
    }

    fn freeze(&self) {
        match MutableStateDecoded::decode(self.0.get()) {
            MutableStateDecoded::Frozen => {}
            MutableStateDecoded::IteratorDepth(0) => {
                self.0.set(MutableStateDecoded::Frozen.encode())
            }
            MutableStateDecoded::IteratorDepth(_) => panic!("attempt to freeze during iteration"),
        }
    }

    /// Freezes the current value for iterating over.
    fn freeze_for_iteration(&self) {
        match MutableStateDecoded::decode(self.0.get()) {
            MutableStateDecoded::Frozen => {}
            MutableStateDecoded::IteratorDepth(n) => self
                .0
                .set(MutableStateDecoded::IteratorDepth(n + 1).encode()),
        }
    }

    /// Unfreezes the current value for iterating over.
    fn unfreeze_for_iteration(&self) {
        match MutableStateDecoded::decode(self.0.get()) {
            MutableStateDecoded::Frozen => {}
            MutableStateDecoded::IteratorDepth(n) => self
                .0
                .set(MutableStateDecoded::IteratorDepth(n.checked_sub(1).unwrap()).encode()),
        }
    }

    fn new() -> Self {
        MutableMutability(Cell::new(MutableStateDecoded::IteratorDepth(0).encode()))
    }
}
