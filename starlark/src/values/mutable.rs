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

//! Common data struct for mutable types.

use crate::environment::Environment;
use crate::values::immutable::ReadableContent;
use crate::values::{default_compare, TypedValue, Value, ValueError, ValueResult};
use linked_hash_map::LinkedHashMap;
use std::any::Any;
use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::ops::Deref;
use std::ops::DerefMut;

/// A helper enum for defining the level of mutability of an iterable.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
enum IterableMutability {
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

/// Mutable object without common header.
pub trait MutableContent: ReadableContent + Default {
    /// Check if `set_at` is implemented for this type.
    fn set_at_check(&self, index: &Value) -> Result<(), ValueError>;

    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError>;

    /// Check if `set_at` is implemented for this type.
    fn set_attr_check(&self, attribute: &str) -> Result<(), ValueError>;

    fn set_attr(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError>;
}

/// Common implementation of mutable data types list, dict and set.
pub struct Mutable<D: MutableContent> {
    mutability: Cell<IterableMutability>,
    pub content: RefCell<D>,
}

impl<D: MutableContent> Default for Mutable<D> {
    fn default() -> Mutable<D> {
        Mutable::new(Default::default())
    }
}

impl<D: MutableContent> Mutable<D> {
    /// Freezes the current value, can be used when implementing the `freeze` function
    /// of the [TypedValue] trait.
    pub fn mutability_freeze(&self) {
        self.mutability.set(IterableMutability::FrozenForIteration)
    }

    pub fn apply<Return>(
        v: &Value,
        f: &dyn Fn(&D) -> Result<Return, ValueError>,
    ) -> Result<Return, ValueError>
    where
        Self: TypedValue,
    {
        v.downcast_apply(|x: &Self| -> Result<Return, ValueError> { f(x.content.borrow().deref()) })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    pub fn mutate(v: &Value, f: &Fn(&mut D) -> ValueResult) -> ValueResult
    where
        Self: TypedValue,
    {
        v.downcast_apply(|x: &Self| -> ValueResult {
            x.mutability.get().test()?;
            f(x.content.borrow_mut().deref_mut())
        })
        .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    pub fn new(content: D) -> Mutable<D> {
        Mutable {
            mutability: Cell::new(IterableMutability::Mutable),
            content: RefCell::new(content),
        }
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new_value(content: D) -> Value
    where
        Self: TypedValue,
    {
        Value::new(Mutable::new(content))
    }
}

impl<D: MutableContent> TypedValue for Mutable<D> {
    fn freeze(&self) {
        self.mutability_freeze();
        for v in self
            .content
            .borrow()
            .values_for_descendant_check_and_freeze()
        {
            v.freeze();
        }
    }

    fn immutable(&self) -> bool {
        self.mutability.get() == IterableMutability::Immutable
    }

    fn freeze_for_iteration(&self) {
        match self.mutability.get() {
            IterableMutability::Immutable => {}
            IterableMutability::FrozenForIteration => panic!("already frozen"),
            IterableMutability::Mutable => {
                self.mutability.set(IterableMutability::FrozenForIteration);
            }
        }
    }

    /// Unfreezes the current value for iterating over, to be used to implement the
    /// `unfreeze_for_iteration` function of the [TypedValue] trait.
    fn unfreeze_for_iteration(&self) {
        match self.mutability.get() {
            IterableMutability::Immutable => {}
            IterableMutability::FrozenForIteration => {
                self.mutability.set(IterableMutability::Mutable);
            }
            IterableMutability::Mutable => {
                panic!("not fronzen");
            }
        }
    }

    fn to_str(&self) -> String {
        self.content.borrow().to_str()
    }

    fn to_repr(&self) -> String {
        self.content.borrow().to_repr()
    }

    fn get_type(&self) -> &'static str {
        D::get_type()
    }
    fn to_bool(&self) -> bool {
        self.content.borrow().to_bool()
    }

    fn compare(&self, other: &dyn TypedValue, recursion: u32) -> Result<Ordering, ValueError> {
        match other.as_any().downcast_ref::<Self>() {
            Some(other) => self
                .content
                .borrow()
                .compare(&other.content.borrow(), recursion),
            None => default_compare(self, other),
        }
    }

    fn at(&self, index: Value) -> ValueResult {
        self.content.borrow().at(index)
    }

    fn length(&self) -> Result<i64, ValueError> {
        self.content.borrow().length()
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        self.content.borrow().is_in(other)
    }

    fn is_descendant(&self, other: &dyn TypedValue) -> bool {
        let try_borrowed = self.content.try_borrow();
        if let Ok(borrowed) = try_borrowed {
            borrowed
                .values_for_descendant_check_and_freeze()
                .any(|x| x.is_descendant(other))
        } else {
            // We have already borrowed mutably this value, which means we are trying to mutate it, assigning other to it.
            true
        }
    }

    fn iter(&self) -> Result<Vec<Value>, ValueError> {
        self.content.borrow().iter()
    }

    fn set_at(&self, index: Value, new_value: Value) -> Result<(), ValueError> {
        self.content.borrow().set_at_check(&index)?;
        self.mutability.get().test()?;
        let new_value = new_value.clone_for_container(self)?;
        self.content.borrow_mut().set_at(index, new_value)
    }

    fn add(&self, other: Value) -> ValueResult {
        other
            .downcast_apply(|other: &Self| {
                let sum = self.content.borrow().add(&other.content.borrow())?;
                Ok(Value::new(Mutable::new(sum)))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn mul(&self, other: Value) -> ValueResult {
        self.content.borrow().mul(other)
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<Value, ValueError> {
        self.content.borrow().slice(start, stop, stride)
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        self.content.borrow().get_hash()
    }

    fn as_any(&self) -> &Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut Any {
        self
    }

    fn to_int(&self) -> Result<i64, ValueError> {
        self.content.borrow().to_int()
    }

    fn call(
        &self,
        call_stack: &[(String, String)],
        env: Environment,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> Result<Value, ValueError> {
        self.content
            .borrow()
            .call(call_stack, env, positional, named, args, kwargs)
    }

    fn get_attr(&self, attribute: &str) -> Result<Value, ValueError> {
        self.content.borrow().get_attr(attribute)
    }

    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        self.content.borrow().has_attr(attribute)
    }

    fn set_attr(&self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        self.content.borrow_mut().set_attr_check(attribute)?;
        let new_value = new_value.clone_for_container(self)?;
        self.content.borrow_mut().set_attr(attribute, new_value)
    }

    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        self.content.borrow().dir_attr()
    }

    fn plus(&self) -> Result<Value, ValueError> {
        self.content.borrow().plus()
    }

    fn minus(&self) -> Result<Value, ValueError> {
        self.content.borrow().minus()
    }

    fn sub(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| {
                Ok(Value::new(Mutable::new(
                    self.content.borrow().sub(&other.content.borrow())?,
                )))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn percent(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().percent(other)
    }

    fn div(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| {
                Ok(Mutable::new_value(
                    self.content.borrow().div(&other.content.borrow())?,
                ))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn floor_div(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| {
                Ok(Mutable::new_value(
                    self.content.borrow().floor_div(&other.content.borrow())?,
                ))
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn pipe(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().pipe(other)
    }
}
