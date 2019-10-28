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

//! Object header

use crate::values::cell::error::ObjectBorrowError;
use crate::values::cell::error::ObjectBorrowMutError;
use std::cell::Cell;
use std::fmt;

/// Object mutability state.
#[derive(PartialEq, Debug)]
enum ObjectState {
    /// Object type is immutable
    Immutable,
    /// Object type is mutable, but object is frozen
    Frozen,
    /// Borrowed mutably
    BorrowedMut,
    /// Borrowed
    // borrowed count, borrowed for iteration
    Borrowed(usize, bool),
}

const IMMUTABLE: usize = usize::max_value();
const FROZEN: usize = usize::max_value() - 1;
const BORROWED_MUT: usize = usize::max_value() - 2;
const FOR_ITER_BIT: usize = (usize::max_value() >> 2) + 1;

impl ObjectState {
    fn encode(&self) -> usize {
        match self {
            ObjectState::Immutable => IMMUTABLE,
            ObjectState::Frozen => FROZEN,
            ObjectState::BorrowedMut => BORROWED_MUT,
            ObjectState::Borrowed(count, for_iter) => {
                let mut r = *count;
                if *for_iter {
                    debug_assert!(*count != 0);
                    r = r | FOR_ITER_BIT;
                }
                r
            }
        }
    }

    fn decode(state: usize) -> ObjectState {
        if state == IMMUTABLE {
            ObjectState::Immutable
        } else if state == FROZEN {
            ObjectState::Frozen
        } else if state == BORROWED_MUT {
            ObjectState::BorrowedMut
        } else {
            let for_iter = (state & FOR_ITER_BIT) != 0;
            let count = state & !FOR_ITER_BIT;
            if for_iter {
                debug_assert!(count != 0);
            }
            ObjectState::Borrowed(count, for_iter)
        }
    }
}

pub(crate) struct ObjectBorrowRef<'b> {
    header: &'b ObjectHeader,
    was_for_iter: bool,
}

impl ObjectBorrowRef<'_> {
    /// Immutable object borrow.
    pub fn immutable() -> ObjectBorrowRef<'static> {
        ObjectBorrowRef {
            // Note returned object is no-op on drop,
            // so that's fine to use a reference to a static variable.
            header: ObjectHeader::immutable_static(),
            was_for_iter: false,
        }
    }
}

pub(crate) struct ObjectBorrowRefMut<'b> {
    header: &'b ObjectHeader,
}

impl Drop for ObjectBorrowRef<'_> {
    fn drop(&mut self) {
        // If `<T>` is immutable, it's possible to implement
        // a micropimization here: static no-op.
        self.header.unborrow(self.was_for_iter);
    }
}

impl Drop for ObjectBorrowRefMut<'_> {
    fn drop(&mut self) {
        self.header.unborrow_mut();
    }
}

impl fmt::Debug for ObjectBorrowRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObjectBorrowRef").field("_", &()).finish()
    }
}

impl fmt::Debug for ObjectBorrowRefMut<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObjectBorrowRefMut")
            .field("_", &())
            .finish()
    }
}

/// Struct to declare unsync `ObjectHeader` in static non-mut field.
struct ObjectHeaderInStaticField(ObjectHeader);
unsafe impl Sync for ObjectHeaderInStaticField {}
static IMMUTABLE_OBJECT_HEADER: ObjectHeaderInStaticField =
    ObjectHeaderInStaticField(ObjectHeader {
        state: Cell::new(IMMUTABLE),
    });

pub(crate) struct ObjectHeader {
    state: Cell<usize>,
}

impl ObjectHeader {
    fn get_decoded(&self) -> ObjectState {
        ObjectState::decode(self.state.get())
    }

    fn set_decoded(&self, state: ObjectState) {
        self.state.set(state.encode());
    }

    /// Create new object header for mutable object
    pub fn mutable() -> ObjectHeader {
        ObjectHeader {
            state: Cell::new(ObjectState::Borrowed(0, false).encode()),
        }
    }

    /// Create new object header for immutable object
    pub fn immutable() -> ObjectHeader {
        ObjectHeader {
            state: Cell::new(ObjectState::Immutable.encode()),
        }
    }

    /// Get a header pointer for immutable object.
    /// Note all operations like `freeze` or `borrow` do not change
    /// bits of the state, so it's safe to pass a pointer to global immutable value.
    pub fn immutable_static() -> &'static ObjectHeader {
        &IMMUTABLE_OBJECT_HEADER.0
    }

    /// Freeze the object.
    pub fn freeze(&self) {
        match self.get_decoded() {
            ObjectState::Frozen => {}
            ObjectState::Immutable => {}
            ObjectState::Borrowed(0, _) => self.set_decoded(ObjectState::Frozen),
            ObjectState::Borrowed(..) => panic!("cannot freeze, because it is borrowed"),
            ObjectState::BorrowedMut => panic!("cannot freeze, because it is borrowed mutably"),
        }
    }

    pub fn try_borrow(&self, for_iter: bool) -> Result<ObjectBorrowRef, ObjectBorrowError> {
        Ok(match self.get_decoded() {
            ObjectState::Frozen => ObjectBorrowRef {
                header: self,
                was_for_iter: false,
            },
            ObjectState::Immutable => ObjectBorrowRef {
                header: self,
                was_for_iter: false,
            },
            ObjectState::Borrowed(count, was_for_iter) => {
                self.set_decoded(ObjectState::Borrowed(count + 1, for_iter || was_for_iter));
                ObjectBorrowRef {
                    header: self,
                    was_for_iter,
                }
            }
            ObjectState::BorrowedMut => {
                return Err(ObjectBorrowError::BorrowedMut);
            }
        })
    }

    fn unborrow(&self, was_for_iter: bool) {
        match self.get_decoded() {
            ObjectState::Frozen => {}
            ObjectState::Immutable => {}
            ObjectState::Borrowed(count, _) => {
                assert!(count > 0);
                self.set_decoded(ObjectState::Borrowed(count - 1, was_for_iter));
            }
            ObjectState::BorrowedMut => {
                panic!("unborrow when borrowed mutably");
            }
        }
    }

    pub fn try_borrow_mut(&self) -> Result<ObjectBorrowRefMut, ObjectBorrowMutError> {
        Err(match self.get_decoded() {
            ObjectState::Immutable => ObjectBorrowMutError::Immutable,
            ObjectState::Frozen => ObjectBorrowMutError::Frozen,
            ObjectState::BorrowedMut => ObjectBorrowMutError::BorrowedMut,
            ObjectState::Borrowed(0, _) => {
                self.set_decoded(ObjectState::BorrowedMut);
                return Ok(ObjectBorrowRefMut { header: self });
            }
            ObjectState::Borrowed(_, true) => ObjectBorrowMutError::FrozenForIteration,
            ObjectState::Borrowed(_, false) => ObjectBorrowMutError::Borrowed,
        })
    }

    fn unborrow_mut(&self) {
        match self.get_decoded() {
            ObjectState::Immutable => unreachable!(),
            ObjectState::Frozen => unreachable!(),
            ObjectState::Borrowed(..) => unreachable!(),
            ObjectState::BorrowedMut => {
                self.set_decoded(ObjectState::Borrowed(0, false));
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn immutable_static() {
        let h = ObjectHeader::immutable_static();
        let b = h.try_borrow(true).unwrap();
        assert_eq!(false, b.was_for_iter);
        assert_eq!(false, h.try_borrow(true).unwrap().was_for_iter);
        drop(b);
        h.freeze();
        assert_eq!(
            ObjectBorrowMutError::Immutable,
            h.try_borrow_mut().unwrap_err()
        );
    }

    #[test]
    fn frozen() {
        let h = ObjectHeader::mutable();
        h.freeze();
        let b = h.try_borrow(false).unwrap();
        assert_eq!(
            ObjectBorrowMutError::Frozen,
            h.try_borrow_mut().unwrap_err()
        );
        assert_eq!(false, h.try_borrow(true).unwrap().was_for_iter);
        drop(b);
        assert_eq!(
            ObjectBorrowMutError::Frozen,
            h.try_borrow_mut().unwrap_err()
        );
    }

    #[test]
    fn mutable_recursive_borrow() {
        let h = ObjectHeader::mutable();
        let b1 = h.try_borrow(true).unwrap();
        let b2 = h.try_borrow(false).unwrap();
        assert_eq!(
            ObjectBorrowMutError::FrozenForIteration,
            h.try_borrow_mut().unwrap_err()
        );
        drop(b2);
        assert_eq!(
            ObjectBorrowMutError::FrozenForIteration,
            h.try_borrow_mut().unwrap_err()
        );
        drop(b1);
        let bm = h.try_borrow_mut().unwrap();
        assert_eq!(
            ObjectBorrowError::BorrowedMut,
            h.try_borrow(true).unwrap_err()
        );
        drop(bm);
    }
}
