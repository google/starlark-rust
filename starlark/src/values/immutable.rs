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

//! Common data struct for immutable types.

use crate::environment::Environment;
use crate::values::{default_compare, TypedValue, Value, ValueError, ValueResult};
use linked_hash_map::LinkedHashMap;
use std::any::Any;
use std::cmp::Ordering;

/// Common interface for mutable and immutable operations.
pub trait ReadableContent: Sized + 'static {
    fn get_type() -> &'static str;

    /// Return a list of values to be used in freeze or descendant check operations.
    fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item = Value> + 'a>;

    fn to_repr(&self) -> String;

    fn to_str(&self) -> String {
        // Delegate to repr by default
        self.to_repr()
    }

    fn to_bool(&self) -> bool;

    fn to_int(&self) -> Result<i64, ValueError>;

    fn at(&self, index: Value) -> ValueResult;

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult;

    fn length(&self) -> Result<i64, ValueError>;

    fn get_hash(&self) -> Result<u64, ValueError>;

    fn is_in(&self, other: &Value) -> Result<bool, ValueError>;

    fn iter(&self) -> Result<Vec<Value>, ValueError>;

    fn plus(&self) -> ValueResult;
    fn minus(&self) -> ValueResult;

    fn add(&self, other: &Self) -> Result<Self, ValueError>;
    fn sub(&self, other: &Self) -> Result<Self, ValueError>;
    fn div(&self, other: &Self) -> Result<Self, ValueError>;
    fn floor_div(&self, other: &Self) -> Result<Self, ValueError>;
    fn mul(&self, other: Value) -> ValueResult;
    fn pipe(&self, other: Value) -> ValueResult;

    fn dir_attr(&self) -> Result<Vec<String>, ValueError>;
    fn has_attr(&self, _attribute: &str) -> Result<bool, ValueError>;
    fn get_attr(&self, attribute: &str) -> ValueResult;

    fn percent(&self, other: Value) -> ValueResult;

    fn compare(&self, other: &Self, recursion: u32) -> Result<Ordering, ValueError>;

    fn call(
        &self,
        call_stack: &[(String, String)],
        env: Environment,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult;
}

pub trait ImmutableContent: ReadableContent {}

pub struct Immutable<D: ImmutableContent> {
    pub content: D,
}

impl<D: ImmutableContent + Default> Default for Immutable<D> {
    fn default() -> Immutable<D> {
        Immutable::new(Default::default())
    }
}

impl<D: ImmutableContent> Immutable<D> {
    pub fn new(content: D) -> Immutable<D> {
        Immutable { content }
    }

    #[allow(clippy::new_ret_no_self)]
    pub fn new_value(value: D) -> Value
    where
        Self: TypedValue,
    {
        Value::new(Immutable { content: value })
    }
}

impl<D: ImmutableContent> TypedValue for Immutable<D> {
    fn immutable(&self) -> bool {
        true
    }

    fn as_any(&self) -> &Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut Any {
        self
    }

    fn freeze(&self) {
        for v in self.content.values_for_descendant_check_and_freeze() {
            v.freeze();
        }
    }

    fn freeze_for_iteration(&self) {}

    fn unfreeze_for_iteration(&self) {}

    fn to_str(&self) -> String {
        self.content.to_str()
    }

    fn to_repr(&self) -> String {
        self.content.to_repr()
    }

    fn get_type(&self) -> &'static str {
        D::get_type()
    }

    fn to_bool(&self) -> bool {
        self.content.to_bool()
    }

    fn to_int(&self) -> Result<i64, ValueError> {
        self.content.to_int()
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        self.content.get_hash()
    }

    fn is_descendant(&self, other: &TypedValue) -> bool {
        self.content
            .values_for_descendant_check_and_freeze()
            .any(|x| x.is_descendant(other))
    }

    fn compare(&self, other: &TypedValue, recursion: u32) -> Result<Ordering, ValueError> {
        match other.as_any().downcast_ref::<Self>() {
            Some(other) => self.content.compare(&other.content, recursion),
            None => default_compare(self, other),
        }
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
            .call(call_stack, env, positional, named, args, kwargs)
    }

    fn at(&self, index: Value) -> Result<Value, ValueError> {
        self.content.at(index)
    }

    fn set_at(&self, index: Value, _new_value: Value) -> Result<(), ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "[] =".to_owned(),
            left: D::get_type().to_owned(),
            right: Some(index.get_type().to_owned()),
        })
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<Value, ValueError> {
        self.content.slice(start, stop, stride)
    }

    fn iter(&self) -> Result<Vec<Value>, ValueError> {
        self.content.iter()
    }

    fn length(&self) -> Result<i64, ValueError> {
        self.content.length()
    }

    fn get_attr(&self, attribute: &str) -> Result<Value, ValueError> {
        self.content.get_attr(attribute)
    }

    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        self.content.has_attr(attribute)
    }

    fn set_attr(&self, attribute: &str, _new_value: Value) -> Result<(), ValueError> {
        Err(ValueError::OperationNotSupported {
            op: format!(".{} =", attribute),
            left: D::get_type().to_owned(),
            right: None,
        })
    }

    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        self.content.dir_attr()
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        self.content.is_in(other)
    }

    fn plus(&self) -> Result<Value, ValueError> {
        self.content.plus()
    }

    fn minus(&self) -> Result<Value, ValueError> {
        self.content.minus()
    }

    fn add(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| self.content.add(&other.content).map(Value::new_imm))
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn sub(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| self.content.sub(&other.content).map(Value::new_imm))
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn mul(&self, other: Value) -> Result<Value, ValueError> {
        self.content.mul(other)
    }

    fn percent(&self, other: Value) -> Result<Value, ValueError> {
        self.content.percent(other)
    }

    fn div(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| self.content.div(&other.content).map(Value::new_imm))
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn floor_div(&self, other: Value) -> Result<Value, ValueError> {
        other
            .downcast_apply(|other: &Self| {
                self.content.floor_div(&other.content).map(Value::new_imm)
            })
            .unwrap_or(Err(ValueError::IncorrectParameterType))
    }

    fn pipe(&self, other: Value) -> Result<Value, ValueError> {
        self.content.pipe(other)
    }
}
