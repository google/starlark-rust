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

//! [`Ref`](std::cell::Ref) and [`RefMut`](std::cell::RefMut)-like objects
//! used in implementation of [`Value`](crate::values::Value).

use crate::values::cell::error::ObjectBorrowError;
use crate::values::cell::error::ObjectBorrowMutError;
use crate::values::cell::header::ObjectBorrowRef;
use crate::values::cell::header::ObjectBorrowRefMut;
use crate::values::cell::header::ObjectHeader;
use std::cell::UnsafeCell;
use std::fmt;
use std::ops::Deref;
use std::ops::DerefMut;

pub mod error;
pub(crate) mod header;

/// [`Ref`](std::cell::Ref)-like object for [`ObjectCell`],
/// and it also works as a reference wrapper for immutable objects.
pub struct ObjectRef<'b, T: ?Sized + 'b> {
    value: &'b T,
    borrow: ObjectBorrowRef<'b>,
}

impl<'b, T: ?Sized + 'b> ObjectRef<'b, T> {
    unsafe fn new(value: &'b UnsafeCell<T>, borrow: ObjectBorrowRef<'b>) -> ObjectRef<'b, T> {
        ObjectRef {
            value: &*value.get(),
            borrow,
        }
    }

    /// A reference to immutable frozen value
    pub fn immutable_frozen(value: &T) -> ObjectRef<T> {
        ObjectRef {
            value,
            borrow: ObjectBorrowRef::immutable_frozen(),
        }
    }

    /// A raw pointer to the referenced value
    pub fn as_ptr(&self) -> *mut T {
        self.value as *const T as *mut T
    }

    /// Convert ref to another type
    pub fn map<U: ?Sized, F>(orig: ObjectRef<'b, T>, f: F) -> ObjectRef<'b, U>
    where
        F: FnOnce(&T) -> &U,
    {
        ObjectRef {
            value: f(orig.value),
            borrow: orig.borrow,
        }
    }

    /// Convert ref to another type
    pub fn flat_map<U: ?Sized, F>(orig: ObjectRef<'b, T>, f: F) -> Option<ObjectRef<'b, U>>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        f(orig.value).map(|value| ObjectRef {
            value,
            borrow: orig.borrow,
        })
    }
}

impl<T: ?Sized> Deref for ObjectRef<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.value
    }
}

/// [`RefMut`](std::cell::RefMut)-like
pub struct ObjectRefMut<'b, T: ?Sized + 'b> {
    value: &'b mut T,
    borrow: ObjectBorrowRefMut<'b>,
}

/// [`RefMut`](std::cell::RefMut)-like
impl<'b, T: ?Sized + 'b> ObjectRefMut<'b, T> {
    pub fn map<U: ?Sized, F>(orig: ObjectRefMut<'b, T>, f: F) -> ObjectRefMut<'b, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        let ObjectRefMut { value, borrow } = orig;
        ObjectRefMut {
            value: f(value),
            borrow,
        }
    }

    pub fn flat_map<U: ?Sized, F>(orig: ObjectRefMut<'b, T>, f: F) -> Option<ObjectRefMut<'b, U>>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        let ObjectRefMut { value, borrow } = orig;
        f(value).map(|value| ObjectRefMut { value, borrow })
    }
}

impl<'b, T: ?Sized + 'b> ObjectRefMut<'b, T> {
    unsafe fn new(value: &'b UnsafeCell<T>, borrow: ObjectBorrowRefMut<'b>) -> ObjectRefMut<'b, T> {
        ObjectRefMut {
            value: &mut *value.get(),
            borrow,
        }
    }
}

impl<T: ?Sized> Deref for ObjectRefMut<'_, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.value
    }
}

impl<T: ?Sized> DerefMut for ObjectRefMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.value
    }
}

/// [`RefCell`](std::cell::RefCell)-like object.
///
/// In addition to `borrow` and `borrow_mut` operation, it also support:
/// * "borrowed for iteration" flag to provide better messages for this Starlark use case
/// * freezing
pub(crate) struct ObjectCell<T: ?Sized> {
    header: ObjectHeader,
    value: UnsafeCell<T>,
}

impl<T> ObjectCell<T> {
    pub fn new_mutable(value: T) -> ObjectCell<T> {
        ObjectCell {
            header: ObjectHeader::mutable(),
            value: UnsafeCell::new(value),
        }
    }

    pub fn new_immutable(value: T) -> ObjectCell<T> {
        ObjectCell {
            header: ObjectHeader::immutable(),
            value: UnsafeCell::new(value),
        }
    }

    pub fn new_immutable_frozen(value: T) -> ObjectCell<T> {
        ObjectCell {
            header: ObjectHeader::immutable_frozen(),
            value: UnsafeCell::new(value),
        }
    }
}

impl<T: ?Sized> ObjectCell<T> {
    pub fn try_borrow(&self, for_iter: bool) -> Result<ObjectRef<T>, ObjectBorrowError> {
        let borrow = self.header.try_borrow(for_iter)?;
        Ok(unsafe { ObjectRef::new(&self.value, borrow) })
    }

    pub fn try_borrow_mut(&self) -> Result<ObjectRefMut<T>, ObjectBorrowMutError> {
        let borrow = self.header.try_borrow_mut()?;
        Ok(unsafe { ObjectRefMut::new(&self.value, borrow) })
    }

    pub fn borrow(&self) -> ObjectRef<T> {
        self.try_borrow(false).unwrap()
    }

    pub fn borrow_mut(&self) -> ObjectRefMut<T> {
        self.try_borrow_mut().unwrap()
    }

    pub fn get_ptr(&self) -> *const T {
        self.value.get() as *const T
    }

    /// Get a copy of object header.
    ///
    /// Cannot return the header reference because it's not safe.
    pub fn get_header_copy(&self) -> ObjectHeader {
        self.header.clone()
    }

    /// Mark value as frozen.
    ///
    /// Return `true` if the object was not frozen before.
    ///
    /// # Panics
    ///
    /// If value is borrowed.
    pub fn freeze(&self) -> bool {
        self.header.freeze()
    }

    /// Get a copy of object header.
    pub fn get_header(&self) -> ObjectHeader {
        self.header.clone()
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for ObjectRef<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.value, f)
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for ObjectRefMut<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.value, f)
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for ObjectCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.try_borrow(false) {
            Ok(v) => f.debug_struct("ObjectCell").field("value", &v).finish(),
            Err(e) => f
                .debug_struct("ObjectCell")
                .field("borrow_error", &e)
                .finish(),
        }
    }
}
