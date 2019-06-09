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

use crate::values::{TypedValue, ValueError};
use std::cell::{BorrowError, Cell, Ref, RefCell, RefMut};
use std::fmt;
use std::ops::Deref;

/// A helper enum for defining the level of mutability of an iterable.
#[derive(PartialEq, Eq, Hash, Debug, Copy, Clone)]
pub enum IterableMutability {
    Mutable,
    Immutable,
    FrozenForIteration,
    GarbageCollected,
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
            IterableMutability::GarbageCollected => Err(ValueError::GarbageCollected),
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
    fn borrow(&self, reason: &'static str) -> RefOrRef<'_, Self::Content>;
    fn try_borrow(&self) -> Result<RefOrRef<Self::Content>, BorrowError>;
    fn borrow_mut(&self, reason: &'static str) -> RefMut<'_, Self::Content>;
    fn clear(&self);
    fn as_ptr(&self) -> *const Self::Content;
}

/// Container for immutable data
#[derive(Debug)]
pub struct ImmutableCell<T>(T);

/// Container for mutable data
#[derive(Debug)]
pub struct MutableCell<T: TypedValue + Default> {
    ref_cell: RefCell<T>,
    last_borrow_reason: Cell<&'static str>,
}

impl<T: TypedValue + Default> RefCellOrImmutable for MutableCell<T> {
    type Content = T;

    fn new(value: T) -> Self {
        MutableCell {
            ref_cell: RefCell::new(value),
            last_borrow_reason: Cell::new("never borrowed"),
        }
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        RefCell::try_borrow(&self.ref_cell).map(RefOrRef::Borrowed)
    }

    fn borrow(&self, reason: &'static str) -> RefOrRef<T> {
        match self.try_borrow() {
            Ok(re) => {
                self.last_borrow_reason.set(reason);
                re
            }
            Err(_) => panic!(
                "cannot borrow immutably: already borrowed for {}",
                self.last_borrow_reason.get()
            ),
        }
    }

    fn borrow_mut(&self, reason: &'static str) -> RefMut<Self::Content> {
        match RefCell::try_borrow_mut(&self.ref_cell) {
            Ok(re) => {
                self.last_borrow_reason.set(reason);
                re
            }
            Err(_) => panic!(
                "cannot borrow {} mutably: already borrowed for {}",
                T::TYPE,
                self.last_borrow_reason.get()
            ),
        }
    }

    fn clear(&self) {
        *self.borrow_mut("clear") = T::default();
    }

    fn as_ptr(&self) -> *const T {
        RefCell::as_ptr(&self.ref_cell)
    }
}

impl<T> RefCellOrImmutable for ImmutableCell<T> {
    type Content = T;

    fn new(value: T) -> Self {
        ImmutableCell(value)
    }

    fn borrow(&self, _reason: &'static str) -> RefOrRef<T> {
        RefOrRef::Ptr(&self.0)
    }

    fn try_borrow(&self) -> Result<RefOrRef<T>, BorrowError> {
        Ok(RefOrRef::Ptr(&self.0))
    }

    fn borrow_mut(&self, reason: &'static str) -> RefMut<Self::Content> {
        panic!(
            "immutable value cannot be mutably borrowed (for {})",
            reason
        );
    }

    fn clear(&self) {
        panic!("immutable cannot be cleared");
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

#[derive(Debug)]
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
            IterableMutability::GarbageCollected => panic!("garbage collected"),
        }
    }

    /// Freezes the current value for iterating over.
    fn freeze_for_iteration(&self) {
        match self.0.get() {
            IterableMutability::Immutable => {}
            IterableMutability::FrozenForIteration => panic!("already frozen"),
            IterableMutability::Mutable => self.0.set(IterableMutability::FrozenForIteration),
            IterableMutability::GarbageCollected => panic!("garbage collected"),
        }
    }

    /// Unfreezes the current value for iterating over.
    fn unfreeze_for_iteration(&self) {
        match self.0.get() {
            IterableMutability::Immutable => {}
            IterableMutability::FrozenForIteration => self.0.set(IterableMutability::Mutable),
            IterableMutability::Mutable => panic!("not frozen"),
            IterableMutability::GarbageCollected => panic!("garbage collected"),
        }
    }

    fn new() -> Self {
        MutableMutability(Cell::new(IterableMutability::Mutable))
    }
}
