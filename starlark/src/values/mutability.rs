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
pub struct MutableMutability(Cell<IterableMutability>);

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

impl MutabilityCell for MutableMutability {
    fn get(&self) -> IterableMutability {
        self.0.get()
    }

    fn freeze(&self) {
        match self.0.get() {
            IterableMutability::FrozenForIteration => panic!("attempt to freeze during iteration"),
            IterableMutability::Immutable => {}
            IterableMutability::Mutable => self.0.set(IterableMutability::Immutable),
        }
    }

    /// Freezes the current value for iterating over.
    fn freeze_for_iteration(&self) {
        match self.0.get() {
            IterableMutability::Immutable => {}
            IterableMutability::FrozenForIteration => panic!("already frozen"),
            IterableMutability::Mutable => self.0.set(IterableMutability::FrozenForIteration),
        }
    }

    /// Unfreezes the current value for iterating over.
    fn unfreeze_for_iteration(&self) {
        match self.0.get() {
            IterableMutability::Immutable => {}
            IterableMutability::FrozenForIteration => self.0.set(IterableMutability::Mutable),
            IterableMutability::Mutable => panic!("not frozen"),
        }
    }

    fn new() -> Self {
        MutableMutability(Cell::new(IterableMutability::Mutable))
    }
}
