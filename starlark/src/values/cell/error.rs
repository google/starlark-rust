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

//! Cell-related errors.

use std::fmt;

/// Error when borrow failed.
#[derive(Debug, Clone, PartialEq)]
pub(crate) enum ObjectBorrowError {
    /// Can only fail if object is mutably borrowed
    BorrowedMut,
}

/// Object cannot be mutably borrowed.
#[derive(Debug, Clone, PartialEq)]
pub enum ObjectBorrowMutError {
    /// Object is immutable
    Immutable,
    /// Object is frozen
    Frozen,
    /// Object is frozen for iteration
    FrozenForIteration,
    /// Object is already mutably borrowed
    BorrowedMut,
    /// Object is borrowed
    Borrowed,
}

impl fmt::Display for ObjectBorrowMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ObjectBorrowMutError::Immutable => write!(f, "Immutable"),
            ObjectBorrowMutError::Frozen => write!(f, "Frozen"),
            ObjectBorrowMutError::FrozenForIteration => {
                write!(f, "Cannot mutate an iterable while iterating")
            }
            ObjectBorrowMutError::BorrowedMut => write!(f, "Borrowed mutably"),
            ObjectBorrowMutError::Borrowed => write!(f, "Borrowed"),
        }
    }
}
