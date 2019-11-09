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
use std::mem;

/// Something is frozen or not frozen.
#[derive(Debug, Clone, PartialEq, Copy)]
pub enum FrozenState {
    Yes,
    No,
}

impl FrozenState {
    fn flag(&self) -> usize {
        match self {
            FrozenState::Yes => FROZEN_FLAG,
            FrozenState::No => 0,
        }
    }
}

/// Object mutability state.
#[derive(PartialEq, Debug)]
enum ObjectState {
    /// Object type is immutable
    Immutable(FrozenState),
    /// Borrowed mutably
    // frozen
    BorrowedMut(FrozenState),
    /// Borrowed
    // frozen, borrowed count, borrowed for iteration
    Mutable(FrozenState, usize, bool),
    /// Object is garbage-collected
    Collected,
}

const LARGEST_PO2: usize = (usize::max_value() >> 1) + 1;
const IMMUTABLE_FLAG: usize = LARGEST_PO2 >> 0;
const FROZEN_FLAG: usize = LARGEST_PO2 >> 1;
const FOR_ITER_FLAG: usize = LARGEST_PO2 >> 2;
const BORROWED_MUT_FLAG: usize = LARGEST_PO2 >> 3;
const COLLECTED: usize = FOR_ITER_FLAG - 1;
const MAX_BORROW_COUNT: usize = COLLECTED - 1;

impl ObjectState {
    fn encode(&self) -> usize {
        match self {
            ObjectState::Immutable(frozen) => IMMUTABLE_FLAG | frozen.flag(),
            ObjectState::BorrowedMut(frozen) => BORROWED_MUT_FLAG | frozen.flag(),
            ObjectState::Mutable(frozen, count, for_iter) => {
                assert!(*count <= MAX_BORROW_COUNT);
                let mut r = *count;
                if *for_iter {
                    debug_assert!(*count != 0);
                    r = r | FOR_ITER_FLAG;
                }
                r = r | frozen.flag();
                r
            }
            ObjectState::Collected => COLLECTED,
        }
    }

    fn decode(state: usize) -> ObjectState {
        if state == IMMUTABLE_FLAG {
            ObjectState::Immutable(FrozenState::No)
        } else if state == FROZEN_FLAG | IMMUTABLE_FLAG {
            ObjectState::Immutable(FrozenState::Yes)
        } else if state == BORROWED_MUT_FLAG {
            ObjectState::BorrowedMut(FrozenState::No)
        } else if state == BORROWED_MUT_FLAG | FROZEN_FLAG {
            ObjectState::BorrowedMut(FrozenState::Yes)
        } else if state == COLLECTED {
            ObjectState::Collected
        } else {
            let for_iter = (state & FOR_ITER_FLAG) != 0;
            let frozen = if (state & FROZEN_FLAG) != 0 {
                FrozenState::Yes
            } else {
                FrozenState::No
            };
            let count = state & !FOR_ITER_FLAG & !FROZEN_FLAG;
            if for_iter {
                debug_assert!(count != 0);
            }
            debug_assert!(count <= MAX_BORROW_COUNT);
            ObjectState::Mutable(frozen, count, for_iter)
        }
    }
}

pub(crate) struct ObjectBorrowRef<'b> {
    header: &'b ObjectHeader,
    was_for_iter: bool,
}

impl ObjectBorrowRef<'_> {
    /// Immutable frozen object borrow.
    pub fn immutable_frozen() -> ObjectBorrowRef<'static> {
        ObjectBorrowRef {
            // Note returned object is no-op on drop,
            // so that's fine to use a reference to a static variable.
            header: ObjectHeader::immutable_frozen_static(),
            was_for_iter: false,
        }
    }
}

pub(crate) struct ObjectBorrowRefMut<'b> {
    header: &'b ObjectHeader,
    // Self-assertion
    frozen: FrozenState,
}

impl ObjectBorrowRefMut<'_> {
    pub fn set_collected(self) {
        self.header.set_collected_from_borrowed_mut();
        mem::forget(self);
    }
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
        self.header.unborrow_mut(self.frozen);
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
static IMMUTABLE_FROZEN_OBJECT_HEADER: ObjectHeaderInStaticField =
    ObjectHeaderInStaticField(ObjectHeader {
        state: Cell::new(IMMUTABLE_FLAG | FROZEN_FLAG),
    });

#[derive(Clone, PartialEq)]
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
            state: Cell::new(ObjectState::Mutable(FrozenState::No, 0, false).encode()),
        }
    }

    /// Create new object header for immutable object
    pub fn immutable() -> ObjectHeader {
        ObjectHeader {
            state: Cell::new(ObjectState::Immutable(FrozenState::No).encode()),
        }
    }

    /// Create new object header for immutable object
    pub fn immutable_frozen() -> ObjectHeader {
        ObjectHeader {
            state: Cell::new(ObjectState::Immutable(FrozenState::Yes).encode()),
        }
    }

    /// Get a header pointer for immutable object.
    /// Note all operations like `freeze` or `borrow` do not change
    /// bits of the state, so it's safe to pass a pointer to global immutable value.
    pub fn immutable_frozen_static() -> &'static ObjectHeader {
        &IMMUTABLE_FROZEN_OBJECT_HEADER.0
    }

    /// Immutable (but not mutable frozen).
    pub fn is_immutable(&self) -> bool {
        match self.get_decoded() {
            ObjectState::Immutable(..) => true,
            _ => false,
        }
    }

    /// Freeze the object.
    pub fn freeze(&self) -> bool {
        match self.get_decoded() {
            ObjectState::Immutable(FrozenState::No) => false,
            ObjectState::Immutable(FrozenState::Yes) => {
                self.set_decoded(ObjectState::Immutable(FrozenState::Yes));
                true
            }
            ObjectState::Mutable(_, 0, for_iter) => {
                debug_assert!(!for_iter);
                self.set_decoded(ObjectState::Mutable(FrozenState::Yes, 0, false));
                true
            }
            ObjectState::Mutable(..) => panic!("cannot freeze, because it is borrowed"),
            ObjectState::BorrowedMut(FrozenState::No) => {
                panic!("cannot freeze, because it is borrowed mutably")
            }
            ObjectState::BorrowedMut(FrozenState::Yes) => {
                panic!("cannot freeze, because it is frozen and borrowed mutably")
            }
            ObjectState::Collected => panic!("cannot freeze, because it is collected"),
        }
    }

    pub fn try_borrow(&self, for_iter: bool) -> Result<ObjectBorrowRef, ObjectBorrowError> {
        Ok(match self.get_decoded() {
            ObjectState::Immutable(..) => ObjectBorrowRef {
                header: self,
                was_for_iter: false,
            },
            ObjectState::Mutable(frozen, count, was_for_iter) => {
                self.set_decoded(ObjectState::Mutable(
                    frozen,
                    count + 1,
                    for_iter || was_for_iter,
                ));
                ObjectBorrowRef {
                    header: self,
                    was_for_iter,
                }
            }
            ObjectState::BorrowedMut(frozen) => {
                return Err(ObjectBorrowError::BorrowedMut(frozen));
            }
            ObjectState::Collected => {
                return Err(ObjectBorrowError::Collected);
            }
        })
    }

    fn unborrow(&self, was_for_iter: bool) {
        match self.get_decoded() {
            ObjectState::Immutable(..) => {}
            ObjectState::Mutable(frozen, count, _) => {
                assert!(count > 0);
                self.set_decoded(ObjectState::Mutable(frozen, count - 1, was_for_iter));
            }
            ObjectState::BorrowedMut(FrozenState::No) => {
                panic!("unborrow when borrowed mutably");
            }
            ObjectState::BorrowedMut(FrozenState::Yes) => {
                panic!("unborrow when borrowed mutably and frozen");
            }
            ObjectState::Collected => {
                panic!("unborrow when garbage collected");
            }
        }
    }

    pub fn try_borrow_mut(
        &self,
        allow_frozen: bool,
    ) -> Result<ObjectBorrowRefMut, ObjectBorrowMutError> {
        Err(match self.get_decoded() {
            ObjectState::Immutable(..) => ObjectBorrowMutError::Immutable,
            ObjectState::BorrowedMut(frozen) => ObjectBorrowMutError::BorrowedMut(frozen),
            ObjectState::Mutable(frozen, 0, _) => {
                if frozen == FrozenState::Yes && !allow_frozen {
                    return Err(ObjectBorrowMutError::Frozen);
                }
                self.set_decoded(ObjectState::BorrowedMut(frozen));
                return Ok(ObjectBorrowRefMut {
                    header: self,
                    frozen,
                });
            }
            ObjectState::Mutable(_, _, true) => ObjectBorrowMutError::FrozenForIteration,
            ObjectState::Mutable(frozen, _, false) => ObjectBorrowMutError::Borrowed(frozen),
            ObjectState::Collected => ObjectBorrowMutError::Collected,
        })
    }

    fn unborrow_mut(&self, _frozen: FrozenState) {
        match self.get_decoded() {
            ObjectState::Immutable(..) => unreachable!(),
            ObjectState::BorrowedMut(frozen) => {
                self.set_decoded(ObjectState::Mutable(frozen, 0, false));
            }
            ObjectState::Collected => unreachable!(),
            ObjectState::Mutable(..) => unreachable!(),
        }
    }

    pub fn set_collected_from_borrowed_mut(&self) {
        match self.get_decoded() {
            ObjectState::BorrowedMut(..) => self.set_decoded(ObjectState::Collected),
            _ => unreachable!(),
        }
    }

    pub fn _set_collected(&self) {
        match self.get_decoded() {
            ObjectState::Collected => {}
            ObjectState::Immutable(..) => {
                // not setting to collected because objects like ints
                // are not collected
            }
            ObjectState::BorrowedMut(..) => panic!("borrowed mutably"),
            ObjectState::Mutable(_, 0, _) => self.set_decoded(ObjectState::Collected),
            ObjectState::Mutable(..) => panic!("borrowed"),
        }
    }
}

impl fmt::Debug for ObjectHeader {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.get_decoded(), f)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn immutable_static() {
        let h = ObjectHeader::immutable_frozen_static();
        let b = h.try_borrow(true).unwrap();
        assert_eq!(false, b.was_for_iter);
        assert_eq!(false, h.try_borrow(true).unwrap().was_for_iter);
        drop(b);
        h.freeze();
        assert_eq!(
            ObjectBorrowMutError::Immutable,
            h.try_borrow_mut(false).unwrap_err()
        );
    }

    #[test]
    fn frozen() {
        let h = ObjectHeader::mutable();
        h.freeze();
        let b = h.try_borrow(false).unwrap();
        assert_eq!(
            ObjectBorrowMutError::Borrowed(FrozenState::Yes),
            h.try_borrow_mut(false).unwrap_err()
        );
        assert_eq!(false, h.try_borrow(true).unwrap().was_for_iter);
        drop(b);
        assert_eq!(
            ObjectBorrowMutError::Frozen,
            h.try_borrow_mut(false).unwrap_err()
        );
    }

    #[test]
    fn mutable_recursive_borrow() {
        let h = ObjectHeader::mutable();
        let b1 = h.try_borrow(true).unwrap();
        let b2 = h.try_borrow(false).unwrap();
        assert_eq!(
            ObjectBorrowMutError::FrozenForIteration,
            h.try_borrow_mut(false).unwrap_err()
        );
        drop(b2);
        assert_eq!(
            ObjectBorrowMutError::FrozenForIteration,
            h.try_borrow_mut(false).unwrap_err()
        );
        drop(b1);
        let bm = h.try_borrow_mut(false).unwrap();
        assert_eq!(
            ObjectBorrowError::BorrowedMut(FrozenState::No),
            h.try_borrow(true).unwrap_err()
        );
        drop(bm);
    }

    fn states_for_test() -> Vec<ObjectHeader> {
        vec![
            ObjectState::Immutable(FrozenState::No),
            ObjectState::Immutable(FrozenState::Yes),
            ObjectState::BorrowedMut(FrozenState::No),
            ObjectState::BorrowedMut(FrozenState::Yes),
            ObjectState::Mutable(FrozenState::No, 0, false),
            ObjectState::Mutable(FrozenState::No, 1, false),
            ObjectState::Mutable(FrozenState::No, 3, false),
            ObjectState::Mutable(FrozenState::Yes, 0, false),
            ObjectState::Mutable(FrozenState::Yes, 1, false),
            ObjectState::Mutable(FrozenState::Yes, 3, false),
            ObjectState::Mutable(FrozenState::No, 1, true),
            ObjectState::Mutable(FrozenState::No, 3, true),
            ObjectState::Mutable(FrozenState::Yes, 1, true),
            ObjectState::Mutable(FrozenState::Yes, 3, true),
            ObjectState::Collected,
        ]
        .into_iter()
        .map(|s| ObjectHeader {
            state: Cell::new(s.encode()),
        })
        .collect()
    }

    #[test]
    fn borrow() {
        for h in states_for_test() {
            for &for_iter in &[true, false] {
                let h1 = h.clone();
                // Borrow may be successful or not,
                // but after unborrow state must be restored
                drop(h1.try_borrow(for_iter));
                assert_eq!(h, h1);
            }
        }
    }

    #[test]
    fn borrow_mut() {
        for h in states_for_test() {
            for &allow_frozen in &[true, false] {
                let h1 = h.clone();
                // Borrow may be successful or not,
                // but after unborrow state must be restored
                drop(h1.try_borrow_mut(allow_frozen));
                assert_eq!(h, h1);
            }
        }
    }
}
