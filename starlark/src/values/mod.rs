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

//! The values module define a trait `TypedValue` that defines the attribute of
//! any value in Starlark and a few macro to help implementing this trait.
//! The `Value` struct defines the actual structure holding a TypedValue. It is mostly used to
//! enable mutable and Rc behavior over a TypedValue.
//! This modules also defines this traits for the basic immutable values: int, bool and NoneType.
//! Sub-modules implement other common types of all Starlark dialect.
//!
//! __Note__: we use _sequence_, _iterable_ and _indexable_ according to the
//! definition in the [Starlark specification](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md#sequence-types).
//! We also use the term _container_ for denoting any of those type that can hold several values.
//!
//!
//! # Defining a new type
//!
//! Defining a new Starlark type can be done by implenting the [`TypedValue`](crate::values::TypedValue)
//! trait. All method of that trait are operation needed by Starlark interpreter to understand the
//! type. Most of `TypedValue` methods are optional with default implementations returning error.
//!
//! For example the `NoneType` trait implementation is the following:
//!
//! ```rust
//! # use starlark::values::{TypedValue, Value, Immutable};
//! # use starlark::values::error::ValueError;
//! # use std::cmp::Ordering;
//! # use std::iter;
//! # use std::fmt;
//! # use std::fmt::Write as _;
//!
//! /// Define the NoneType type
//! pub enum NoneType {
//!     None
//! }
//!
//! impl TypedValue for NoneType {
//!     type Holder = Immutable<Self>;
//!     const TYPE: &'static str = "NoneType";
//!
//!     fn compare(&self, _other: &NoneType) -> Result<Ordering, ValueError> {
//!         Ok(Ordering::Equal)
//!     }
//!     fn equals(&self, _other: &NoneType) -> Result<bool, ValueError> {
//!         Ok(true)
//!     }
//!     fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item=Value> + 'a> {
//!         Box::new(iter::empty())
//!     }
//!     fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
//!         write!(buf, "None")
//!     }
//!     fn to_bool(&self) -> bool {
//!         false
//!     }
//!     // just took the result of hash(None) in macos python 2.7.10 interpreter.
//!     fn get_hash(&self) -> Result<u64, ValueError> {
//!         Ok(9_223_380_832_852_120_682)
//!     }
//! }
//! ```
//!
//! In addition to the `TypedValue` trait, it is recommended to implement the `From` trait
//! for all type that can convert to the added type but parameterized it with the `Into<Value>`
//! type. For example the unary tuple `From` trait is defined as followed:
//!
//! ```rust,ignore
//! impl<T: Into<Value>> From<(T,)> for Tuple {
//!     fn from(a: (T,)) -> Tuple {
//!         Tuple { content: vec![a.0.into()] }
//!     }
//! }
//! ```
use crate::environment::TypeValues;
use crate::eval::call_stack;
use crate::eval::call_stack::CallStack;
use crate::values::error::ValueError;
use crate::values::iter::{FakeTypedIterable, RefIterable, TypedIterable};
use codemap_diagnostic::Level;
use linked_hash_map::LinkedHashMap;
use std::any::type_name;
use std::any::Any;
use std::cmp::Ordering;
use std::fmt;
use std::fmt::Write as _;
use std::marker;
use std::rc::Rc;
use std::usize;

/// Similar to [`Value`], but for specific type.
pub(crate) struct ValueOther<T: TypedValue + ?Sized>(Rc<ValueHolder<T>>);

impl<T: TypedValue + Default> Default for ValueOther<T> {
    fn default() -> Self {
        ValueOther::new(T::default())
    }
}

impl<T: TypedValue + ?Sized> Clone for ValueOther<T> {
    fn clone(&self) -> Self {
        ValueOther(self.0.clone())
    }
}

impl<T: TypedValue> ValueOther<T> {
    pub fn new(v: T) -> ValueOther<T> {
        assert!(!T::INLINE);

        ValueOther(Rc::new(ValueHolder {
            value: if T::Holder::MUTABLE {
                ObjectCell::new_mutable(v)
            } else {
                ObjectCell::new_immutable(v)
            },
        }))
    }

    pub fn borrow_mut(&self) -> ObjectRefMut<T> {
        self.0.value.borrow_mut()
    }
}

impl<T: TypedValue + ?Sized> From<ValueOther<T>> for Value {
    fn from(v: ValueOther<T>) -> Self {
        Value(ValueInner::Other(v.0))
    }
}

impl<T: TypedValue> fmt::Debug for ValueOther<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let value: Value = self.clone().into();
        fmt::Debug::fmt(&value, f)
    }
}

/// ValueInner wraps the actual value or a memory pointer
/// to the actual value for complex type.
#[derive(Clone)]
enum ValueInner {
    None(NoneType),
    Bool(bool),
    Int(i64),
    Other(Rc<ValueHolder<dyn TypedValueDyn>>),
}

/// A value in Starlark.
///
/// This is a wrapper around a [TypedValue] which is cheap to clone and safe to pass around.
#[derive(Clone)]
pub struct Value(ValueInner);

pub type ValueResult = Result<Value, ValueError>;

impl Value {
    /// Create a new `Value` from a static value.
    pub fn new<T: TypedValue>(t: T) -> Value {
        t.new_value()
    }

    fn try_value_holder(
        &self,
        for_iter: bool,
    ) -> Result<ObjectRef<dyn TypedValueDyn>, ObjectBorrowError> {
        match &self.0 {
            ValueInner::None(n) => Ok(ObjectRef::immutable_frozen(n)),
            ValueInner::Int(i) => Ok(ObjectRef::immutable_frozen(i)),
            ValueInner::Bool(b) => Ok(ObjectRef::immutable_frozen(b)),
            ValueInner::Other(rc) => rc.value.try_borrow(for_iter),
        }
    }

    /// Get a copy of the object header
    fn object_header_copy(&self) -> ObjectHeader {
        match &self.0 {
            ValueInner::None(..) | ValueInner::Int(..) | ValueInner::Bool(..) => {
                ObjectHeader::immutable_frozen()
            }
            ValueInner::Other(rc) => rc.value.get_header_copy(),
        }
    }

    fn value_holder(&self) -> ObjectRef<dyn TypedValueDyn> {
        self.try_value_holder(false).unwrap()
    }

    fn try_value_holder_mut(
        &self,
    ) -> Result<ObjectRefMut<dyn TypedValueDyn>, ObjectBorrowMutError> {
        match &self.0 {
            ValueInner::Other(rc) => rc.value.try_borrow_mut(),
            _ => Err(ObjectBorrowMutError::Immutable),
        }
    }

    /// Clone for inserting into the other container, using weak reference if we do a
    /// recursive insertion.
    pub fn clone_for_container<T: TypedValue>(&self, container: &T) -> Result<Value, ValueError> {
        if self.is_descendant(DataPtr::from(container)) {
            Err(ValueError::UnsupportedRecursiveDataStructure)
        } else {
            Ok(self.clone())
        }
    }

    pub fn clone_for_container_value(&self, other: &Value) -> Result<Value, ValueError> {
        if self.is_descendant_value(other) {
            Err(ValueError::UnsupportedRecursiveDataStructure)
        } else {
            Ok(self.clone())
        }
    }

    /// Check is the object is frozen.
    pub(crate) fn is_frozen(&self) -> bool {
        self.object_header_copy().is_frozen()
    }

    /// Determine if the value pointed by other is a descendant of self
    pub fn is_descendant_value(&self, other: &Value) -> bool {
        self.is_descendant(other.data_ptr())
    }

    pub fn is_descendant(&self, other: DataPtr) -> bool {
        match self.try_value_holder(false) {
            Ok(v) => v.is_descendant_dyn(other),
            Err(..) => {
                // We have already borrowed mutably this value,
                // which means we are trying to mutate it, assigning other to it.
                true
            }
        }
    }

    /// Object data pointer.
    pub fn data_ptr(&self) -> DataPtr {
        match &self.0 {
            ValueInner::None(n) => DataPtr::from(n),
            ValueInner::Int(i) => DataPtr::from(i),
            ValueInner::Bool(b) => DataPtr::from(b),
            ValueInner::Other(rc) => rc.data_ptr(),
        }
    }

    /// Function id used to detect recursion.
    pub fn function_id(&self) -> FunctionId {
        self.value_holder().function_id_dyn()
    }

    pub(crate) fn inspect(&self) -> StarlarkStruct {
        let header = match &self.0 {
            ValueInner::Bool(..) | ValueInner::Int(..) | ValueInner::None(..) => {
                format!("{:?}", ObjectHeader::immutable_frozen_static())
            }
            ValueInner::Other(rc) => format!("{:?}", rc.value.get_header()),
        };

        let mut fields = LinkedHashMap::new();
        fields.insert(
            "data_ptr".to_owned(),
            Value::from(self.data_ptr().0 as usize),
        );
        let Inspect {
            rust_type_name,
            custom,
        } = self.value_holder().inspect_dyn();
        fields.insert("rust_type_name".to_owned(), Value::from(rust_type_name));
        fields.insert("header".to_owned(), Value::from(header));
        fields.insert("custom".to_owned(), custom);
        StarlarkStruct::new(fields)
    }
}

pub trait Mutability {
    type Content: TypedValue;

    /// This type is mutable or immutable.
    const MUTABLE: bool;
}

/// Type parameter for immutable types.
pub struct Immutable<T>(marker::PhantomData<T>);
/// Type parameter for mutable types.
pub struct Mutable<T>(marker::PhantomData<T>);

impl<T: TypedValue> Mutability for Mutable<T> {
    type Content = T;
    const MUTABLE: bool = true;
}

impl<T: TypedValue> Mutability for Immutable<T> {
    type Content = T;
    const MUTABLE: bool = false;
}

/// Pointer to data, used for cycle checks.
#[derive(Copy, Clone, Debug, Eq)]
pub struct DataPtr(pub(crate) *const ());

impl<T: TypedValue + ?Sized> From<*const T> for DataPtr {
    fn from(p: *const T) -> Self {
        DataPtr(p as *const ())
    }
}

impl<T: TypedValue + ?Sized> From<*mut T> for DataPtr {
    fn from(p: *mut T) -> Self {
        DataPtr::from(p as *const T)
    }
}

impl<T: TypedValue + ?Sized> From<&'_ T> for DataPtr {
    fn from(p: &T) -> Self {
        DataPtr::from(p as *const T)
    }
}

impl From<&'_ dyn TypedValueDyn> for DataPtr {
    fn from(p: &'_ dyn TypedValueDyn) -> Self {
        DataPtr(p as *const dyn TypedValueDyn as *const ())
    }
}

impl From<Value> for DataPtr {
    fn from(v: Value) -> Self {
        v.data_ptr()
    }
}

impl PartialEq for DataPtr {
    fn eq(&self, other: &DataPtr) -> bool {
        self.0 == other.0
    }
}

/// Function identity to detect recursion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionId(pub DataPtr);

impl<T: TypedValue> TypedValueDyn for T {
    fn as_any_ref(&self) -> &dyn Any {
        self as &dyn Any
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self as &mut dyn Any
    }

    fn function_id_dyn(&self) -> FunctionId {
        self.function_id()
            .unwrap_or(FunctionId(DataPtr::from(self)))
    }

    /// Freezes the current value.
    fn freeze_dyn(&self) {
        for mut value in self.values_for_descendant_check_and_freeze() {
            value.freeze();
        }
    }

    fn to_str_impl_dyn(&self, buf: &mut String) -> fmt::Result {
        self.to_str_impl(buf)
    }

    fn to_repr_impl_dyn(&self, buf: &mut String) -> fmt::Result {
        self.to_repr_impl(buf)
    }

    fn get_type_dyn(&self) -> &'static str {
        T::TYPE
    }

    fn to_bool_dyn(&self) -> bool {
        self.to_bool()
    }

    fn to_int_dyn(&self) -> Result<i64, ValueError> {
        self.to_int()
    }

    fn get_hash_dyn(&self) -> Result<u64, ValueError> {
        self.get_hash()
    }

    fn is_descendant_dyn(&self, other: DataPtr) -> bool {
        if DataPtr::from(self) == other {
            return true;
        }
        self.values_for_descendant_check_and_freeze()
            .any(|x| x.is_descendant(other))
    }

    fn equals_dyn(&self, other: &Value) -> Result<bool, ValueError> {
        let _stack_depth_guard = call_stack::try_inc()?;

        match other.downcast_ref::<T>() {
            Some(other) => self.equals(&*other),
            None => Ok(false),
        }
    }

    fn compare_dyn(&self, other: &Value) -> Result<Ordering, ValueError> {
        let _stack_depth_guard = call_stack::try_inc()?;

        match other.downcast_ref::<T>() {
            Some(other) => self.compare(&*other),
            None => Err(ValueError::OperationNotSupported {
                op: "compare".to_owned(),
                left: self.get_type_dyn().to_owned(),
                right: Some(other.get_type().to_owned()),
            }),
        }
    }

    fn call_dyn(
        &self,
        call_stack: &mut CallStack,
        type_values: &TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        self.call(call_stack, type_values, positional, named, args, kwargs)
    }

    fn at_dyn(&self, index: Value) -> Result<Value, ValueError> {
        self.at(index)
    }

    fn set_at_dyn(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        self.set_at(index, new_value)
    }

    fn slice_dyn(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<Value, ValueError> {
        self.slice(start, stop, stride)
    }

    fn iter_dyn<'a>(&'a self) -> Result<&'a dyn TypedIterable, ValueError> {
        self.iter()
    }

    fn length_dyn(&self) -> Result<i64, ValueError> {
        self.length()
    }

    fn get_attr_dyn(&self, attribute: &str) -> Result<Value, ValueError> {
        self.get_attr(attribute)
    }

    fn has_attr_dyn(&self, attribute: &str) -> Result<bool, ValueError> {
        self.has_attr(attribute)
    }

    fn set_attr_dyn(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        self.set_attr(attribute, new_value)
    }

    fn dir_attr_dyn(&self) -> Result<Vec<String>, ValueError> {
        self.dir_attr()
    }

    fn is_in_dyn(&self, other: &Value) -> Result<bool, ValueError> {
        self.is_in(other)
    }

    fn plus_dyn(&self) -> Result<Value, ValueError> {
        self.plus().map(Value::new)
    }

    fn minus_dyn(&self) -> Result<Value, ValueError> {
        self.minus().map(Value::new)
    }

    fn add_dyn(&self, other: Value) -> Result<Value, ValueError> {
        match other.downcast_ref::<T>() {
            Some(other) => self.add(&*other).map(Value::new),
            None => Err(ValueError::IncorrectParameterType),
        }
    }

    fn sub_dyn(&self, other: Value) -> Result<Value, ValueError> {
        match other.downcast_ref() {
            Some(other) => self.sub(&*other).map(Value::new),
            None => Err(ValueError::IncorrectParameterType),
        }
    }

    fn mul_dyn(&self, other: Value) -> Result<Value, ValueError> {
        self.mul(other)
    }

    fn percent_dyn(&self, other: Value) -> Result<Value, ValueError> {
        self.percent(other)
    }

    fn div_dyn(&self, other: Value) -> Result<Value, ValueError> {
        self.div(other)
    }

    fn floor_div_dyn(&self, other: Value) -> Result<Value, ValueError> {
        self.floor_div(other)
    }

    fn pipe_dyn(&self, other: Value) -> Result<Value, ValueError> {
        self.pipe(other)
    }

    fn inspect_dyn(&self) -> Inspect {
        Inspect {
            rust_type_name: type_name::<T>(),
            custom: self.inspect_custom(),
        }
    }
}

/// Used in `inspect` function implementation.
pub(crate) struct Inspect {
    rust_type_name: &'static str,
    custom: Value,
}

struct ValueHolder<T: TypedValueDyn + ?Sized> {
    value: ObjectCell<T>,
}

impl ValueHolder<dyn TypedValueDyn> {
    /// Pointer to `TypedValue` object, used for cycle checks.
    fn data_ptr(&self) -> DataPtr {
        DataPtr(self.value.get_ptr() as *const ())
    }
}

/// Dynamically-dispatched version of [`ValueHolder`].
pub(crate) trait TypedValueDyn: 'static {
    fn as_any_ref(&self) -> &dyn Any;

    fn as_any_mut(&mut self) -> &mut dyn Any;

    /// Id used to detect recursion (which is prohibited in Starlark)
    fn function_id_dyn(&self) -> FunctionId;

    fn freeze_dyn(&self);

    fn to_str_impl_dyn(&self, buf: &mut String) -> fmt::Result;

    fn to_repr_impl_dyn(&self, buf: &mut String) -> fmt::Result;

    fn get_type_dyn(&self) -> &'static str;

    fn to_bool_dyn(&self) -> bool;

    fn to_int_dyn(&self) -> Result<i64, ValueError>;

    fn get_hash_dyn(&self) -> Result<u64, ValueError>;

    fn is_descendant_dyn(&self, other: DataPtr) -> bool;

    fn equals_dyn(&self, other: &Value) -> Result<bool, ValueError>;
    fn compare_dyn(&self, other: &Value) -> Result<Ordering, ValueError>;

    fn call_dyn(
        &self,
        call_stack: &mut CallStack,
        type_values: &TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult;

    fn at_dyn(&self, index: Value) -> ValueResult;

    fn set_at_dyn(&mut self, index: Value, new_value: Value) -> Result<(), ValueError>;
    fn slice_dyn(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult;

    fn iter_dyn(&self) -> Result<&dyn TypedIterable, ValueError>;

    fn length_dyn(&self) -> Result<i64, ValueError>;

    fn get_attr_dyn(&self, attribute: &str) -> ValueResult;

    fn has_attr_dyn(&self, _attribute: &str) -> Result<bool, ValueError>;

    fn set_attr_dyn(&mut self, attribute: &str, _new_value: Value) -> Result<(), ValueError>;

    fn dir_attr_dyn(&self) -> Result<Vec<String>, ValueError>;

    fn is_in_dyn(&self, other: &Value) -> Result<bool, ValueError>;

    fn plus_dyn(&self) -> ValueResult;

    fn minus_dyn(&self) -> ValueResult;

    fn add_dyn(&self, other: Value) -> ValueResult;

    fn sub_dyn(&self, other: Value) -> ValueResult;

    fn mul_dyn(&self, other: Value) -> ValueResult;

    fn percent_dyn(&self, other: Value) -> ValueResult;

    fn div_dyn(&self, other: Value) -> ValueResult;

    fn floor_div_dyn(&self, other: Value) -> ValueResult;

    fn pipe_dyn(&self, other: Value) -> ValueResult;

    fn inspect_dyn(&self) -> Inspect;
}

/// A trait for a value with a type that all variable container
/// will implement.
pub trait TypedValue: Sized + 'static {
    /// Must be either `MutableHolder<Self>` or `ImmutableHolder<Self>`
    type Holder: Mutability<Content = Self>;

    /// Return a string describing the type of self, as returned by the type() function.
    const TYPE: &'static str;

    /// True iff value is stored inline in [`Value`] (instead of in [`Rc`]).
    #[doc(hidden)]
    const INLINE: bool = false;

    /// Create a value for `TypedValue`.
    ///
    /// This function should be overridden only by builtin types.
    #[doc(hidden)]
    fn new_value(self) -> Value {
        ValueOther::new(self).into()
    }

    /// Return a list of values to be used in freeze or descendant check operations.
    ///
    /// Objects which do not contain references to other Starlark objects typically
    /// implement it by returning an empty iterator:
    ///
    /// ```
    /// # use starlark::values::*;
    /// # use std::iter;
    /// # struct MyType;
    ///
    /// # impl TypedValue for MyType {
    /// #    type Holder = Immutable<MyType>;
    /// #    const TYPE: &'static str = "MyType";
    /// #
    /// fn values_for_descendant_check_and_freeze<'a>(&'a self) -> Box<Iterator<Item=Value> + 'a> {
    ///     Box::new(iter::empty())
    /// }
    /// #
    /// # }
    /// ```
    fn values_for_descendant_check_and_freeze<'a>(&'a self)
        -> Box<dyn Iterator<Item = Value> + 'a>;

    /// Return function id to detect recursion.
    ///
    /// If `None` is returned, object id is used.
    fn function_id(&self) -> Option<FunctionId> {
        None
    }

    /// Return a string describing of self, as returned by the str() function.
    fn to_str(&self) -> String {
        let mut buf = String::new();
        self.to_str_impl(&mut buf).unwrap();
        buf
    }

    /// The implementation of `to_str`, more efficient for nested objects
    fn to_str_impl(&self, buf: &mut String) -> fmt::Result {
        self.to_repr_impl(buf)
    }

    /// Return a string representation of self, as returned by the repr() function.
    fn to_repr(&self) -> String {
        let mut buf = String::new();
        self.to_repr_impl(&mut buf).unwrap();
        buf
    }

    /// The implementation of `to_repr`, more efficient for nested objects
    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        write!(buf, "<{}>", Self::TYPE)
    }

    /// Convert self to a Boolean truth value, as returned by the bool() function.
    fn to_bool(&self) -> bool {
        // Return `true` by default, because this is default when implementing
        // custom types in Python: https://docs.python.org/release/2.5.2/lib/truth.html
        true
    }

    /// Convert self to a integer value, as returned by the int() function if the type is numeric
    /// (not for string).
    fn to_int(&self) -> Result<i64, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "int()".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Return a hash code for self, as returned by the hash() function, or
    /// OperationNotSupported if there is no hash for this value (e.g. list).
    fn get_hash(&self) -> Result<u64, ValueError> {
        Err(ValueError::NotHashableValue)
    }

    /// Compare `self` with `other` for equality.
    ///
    /// `other` parameter is of type `Self` so it is safe to downcast it.
    ///
    /// Default implementation does pointer (id) comparison.
    ///
    /// Note: `==` in Starlark should work for arbitary objects,
    /// so implementation should avoid returning errors except for
    //  unrecoverable runtime errors.
    fn equals(&self, other: &Self) -> Result<bool, ValueError> {
        let self_ptr = self as *const Self as *const ();
        let other_ptr = other as *const Self as *const ();
        Ok(self_ptr == other_ptr)
    }

    /// Compare `self` with `other`.
    ///
    /// This method returns a result of type [`Ordering`].
    ///
    /// `other` parameter is of type `Self` so it is safe to downcast it.
    ///
    /// Default implementation returns error.
    ///
    /// __Note__: This does not use the [`PartialOrd`] trait as
    ///       the trait needs to know the actual type of the value we compare.
    fn compare(&self, _other: &Self) -> Result<Ordering, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "compare".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(Self::TYPE.to_owned()),
        })
    }

    /// Perform a call on the object, only meaningfull for function object.
    ///
    /// For instance, if this object is a callable (i.e. a function or a method) that adds 2
    /// integers then `self.call(vec![Value::new(1), Value::new(2)], HashMap::new(),
    /// None, None)` would return `Ok(Value::new(3))`.
    ///
    /// # Parameters
    ///
    /// * call_stack: the calling stack, to detect recursion
    /// * type_values: environment used to resolve type fields.
    /// * positional: the list of arguments passed positionally.
    /// * named: the list of argument that were named.
    /// * args: if provided, the `*args` argument.
    /// * kwargs: if provided, the `**kwargs` argument.
    fn call(
        &self,
        _call_stack: &mut CallStack,
        _type_values: &TypeValues,
        _positional: Vec<Value>,
        _named: LinkedHashMap<String, Value>,
        _args: Option<Value>,
        _kwargs: Option<Value>,
    ) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "call()".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Perform an array or dictionary indirection.
    ///
    /// This returns the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "[]".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(index.get_type().to_owned()),
        })
    }

    /// Set the value at `index` with `new_value`.
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue` if the value was
    /// frozen (but with `ValueError::OperationNotSupported` if the operation is not supported
    /// on this value, even if the value is immutable, e.g. for numbers).
    fn set_at(&mut self, index: Value, _new_value: Value) -> Result<(), ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "[] =".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(index.get_type().to_owned()),
        })
    }

    /// Extract a slice of the underlying object if the object is indexable. The result will be
    /// object between `start` and `stop` (both of them are added length() if negative and then
    /// clamped between 0 and length()). `stride` indicates the direction.
    ///
    /// # Parameters
    ///
    /// * start: the start of the slice.
    /// * stop: the end of the slice.
    /// * stride: the direction of slice,
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// // Remove the first element: "abc"[1:] == "bc".
    /// Value::from("abc").slice(Some(Value::from(1)), None, None).unwrap() == Value::from("bc")
    /// # );
    /// # assert!(
    /// // Remove the last element: "abc"[:-1] == "ab".
    /// Value::from("abc").slice(None, Some(Value::from(-1)), None).unwrap()
    ///    == Value::from("ab")
    /// # );
    /// # assert!(
    /// // Remove the first and the last element: "abc"[1:-1] == "b".
    /// Value::from("abc").slice(Some(Value::from(1)), Some(Value::from(-1)), None).unwrap()
    ///    == Value::from("b")
    /// # );
    /// # assert!(
    /// // Select one element out of 2, skipping the first: "banana"[1::2] == "aaa".
    /// Value::from("banana").slice(Some(Value::from(1)), None, Some(Value::from(2))).unwrap()
    ///    == Value::from("aaa")
    /// # );
    /// # assert!(
    /// // Select one element out of 2 in reverse order, starting at index 4:
    /// //   "banana"[4::-2] = "nnb"
    /// Value::from("banana").slice(Some(Value::from(4)), None, Some(Value::from(-2))).unwrap()
    ///    == Value::from("nnb")
    /// # );
    /// ```
    fn slice(
        &self,
        _start: Option<Value>,
        _stop: Option<Value>,
        _stride: Option<Value>,
    ) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "[::]".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Returns an iterable over the value of this container if this value hold an iterable
    /// container.
    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Err(ValueError::TypeNotX {
            object_type: Self::TYPE.to_owned(),
            op: "iterable".to_owned(),
        })
    }

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> Result<i64, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "len()".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Get an attribute for the current value as would be returned by dotted expression (i.e.
    /// `a.attribute`).
    ///
    /// __Note__: this does not handle native methods which are handled through universe.
    fn get_attr(&self, attribute: &str) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: format!(".{}", attribute),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Return true if an attribute of name `attribute` exists for the current value.
    ///
    /// __Note__: this does not handle native methods which are handled through universe.
    fn has_attr(&self, _attribute: &str) -> Result<bool, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "has_attr()".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Set the attribute named `attribute` of the current value to `new_value` (e.g.
    /// `a.attribute = new_value`).
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue` if the value was
    /// frozen or the attribute is immutable (but with `ValueError::OperationNotSupported`
    /// if the operation is not supported on this value, even if the self is immutable,
    /// e.g. for numbers).
    fn set_attr(&mut self, attribute: &str, _new_value: Value) -> Result<(), ValueError> {
        Err(ValueError::OperationNotSupported {
            op: format!(".{} =", attribute),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Return a vector of string listing all attribute of the current value, excluding native
    /// methods.
    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "dir()".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Tell wether `other` is in the current value, if it is a container.
    ///
    /// Non container value should return an error `ValueError::OperationNotSupported`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// // "a" in "abc" == True
    /// assert!(Value::from("abc").is_in(&Value::from("a")).unwrap().to_bool());
    /// // "b" in "abc" == True
    /// assert!(Value::from("abc").is_in(&Value::from("b")).unwrap().to_bool());
    /// // "z" in "abc" == False
    /// assert!(!Value::from("abc").is_in(&Value::from("z")).unwrap().to_bool());
    /// ```
    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "in".to_owned(),
            left: other.get_type().to_owned(),
            right: Some(Self::TYPE.to_owned()),
        })
    }

    /// Apply the `+` unary operator to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(1, int_op!(1.plus()));  // 1.plus() = +1 = 1
    /// # }
    /// ```
    fn plus(&self) -> Result<Self, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "+".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Apply the `-` unary operator to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(-1, int_op!(1.minus()));  // 1.minus() = -1
    /// # }
    /// ```
    fn minus(&self) -> Result<Self, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "-".to_owned(),
            left: Self::TYPE.to_owned(),
            right: None,
        })
    }

    /// Add `other` to the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(3, int_op!(1.add(2)));  // 1.add(2) = 1 + 2 = 3
    /// # }
    /// ```
    fn add(&self, _other: &Self) -> Result<Self, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "+".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(Self::TYPE.to_owned()),
        })
    }

    /// Substract `other` from the current value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(-1, int_op!(1.sub(2)));  // 1.sub(2) = 1 - 2 = -1
    /// # }
    /// ```
    fn sub(&self, _other: &Self) -> Result<Self, ValueError> {
        Err(ValueError::OperationNotSupported {
            op: "-".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(Self::TYPE.to_owned()),
        })
    }

    /// Multiply the current value with `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(6, int_op!(2.mul(3)));  // 2.mul(3) = 2 * 3 = 6
    /// # }
    /// ```
    fn mul(&self, other: Value) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "*".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(other.get_type().to_owned()),
        })
    }

    /// Apply the percent operator between the current value and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # use starlark::values::string;
    /// # fn main() {
    /// // Remainder of the floored division: 5.percent(3) = 5 % 3 = 2
    /// assert_eq!(2, int_op!(5.percent(3)));
    /// // String formatting: "a {} c" % 3 == "a 3 c"
    /// assert_eq!(Value::from("a 3 c"), Value::from("a %s c").percent(Value::from(3)).unwrap());
    /// # }
    /// ```
    fn percent(&self, other: Value) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "%".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(other.get_type().to_owned()),
        })
    }

    /// Divide the current value with `other`.  division.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(3, int_op!(7.div(2)));  // 7.div(2) = 7 / 2 = 3
    /// # }
    /// ```
    fn div(&self, other: Value) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "/".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(other.get_type().to_owned()),
        })
    }

    /// Floor division between the current value and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[macro_use] extern crate starlark;
    /// # use starlark::values::*;
    /// # fn main() {
    /// assert_eq!(3, int_op!(7.floor_div(2)));  // 7.div(2) = 7 / 2 = 3
    /// # }
    /// ```
    fn floor_div(&self, other: Value) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "//".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(other.get_type().to_owned()),
        })
    }

    /// Apply the operator pipe to the current value and `other`.
    ///
    /// This is usually the union on set.
    fn pipe(&self, other: Value) -> ValueResult {
        Err(ValueError::OperationNotSupported {
            op: "|".to_owned(),
            left: Self::TYPE.to_owned(),
            right: Some(other.get_type().to_owned()),
        })
    }

    /// Provide custom fields for `inspect` function
    #[doc(hidden)]
    fn inspect_custom(&self) -> Value {
        Value::new(NoneType::None)
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Value[{}]({})", self.get_type(), self.to_repr())
    }
}

impl Value {
    pub fn freeze(&mut self) {
        match &self.0 {
            ValueInner::Other(rc) => {
                if rc.value.freeze() {
                    // Only freeze content if the object was not frozen earlier
                    self.value_holder().freeze_dyn();
                }
            }
            _ => {
                // `None`, `bool`, `int` are frozen at construction
            }
        }
    }
    pub fn to_str_impl(&self, buf: &mut String) -> fmt::Result {
        self.value_holder().to_str_impl_dyn(buf)
    }
    pub fn to_str(&self) -> String {
        let mut buf = String::new();
        self.to_str_impl(&mut buf).unwrap();
        buf
    }
    pub fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        self.value_holder().to_repr_impl_dyn(buf)
    }
    pub fn to_repr(&self) -> String {
        let mut buf = String::new();
        self.to_repr_impl(&mut buf).unwrap();
        buf
    }
    pub fn get_type(&self) -> &'static str {
        self.value_holder().get_type_dyn()
    }
    pub fn to_bool(&self) -> bool {
        self.value_holder().to_bool_dyn()
    }
    pub fn to_int(&self) -> Result<i64, ValueError> {
        self.value_holder().to_int_dyn()
    }
    pub fn get_hash(&self) -> Result<u64, ValueError> {
        self.value_holder().get_hash_dyn()
    }
    pub fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        self.value_holder().equals_dyn(other)
    }
    pub fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        self.value_holder().compare_dyn(other)
    }

    pub fn call(
        &self,
        call_stack: &mut CallStack,
        type_values: &TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        self.value_holder()
            .call_dyn(call_stack, type_values, positional, named, args, kwargs)
    }

    pub fn at(&self, index: Value) -> ValueResult {
        self.value_holder().at_dyn(index)
    }

    pub fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        match self.try_value_holder_mut() {
            Err(ObjectBorrowMutError::Immutable) => {
                return Err(ValueError::OperationNotSupported {
                    op: "[] =".to_owned(),
                    left: self.get_type().to_owned(),
                    right: Some(index.get_type().to_owned()),
                });
            }
            Err(e) => Err(e.into()),
            Ok(mut v) => v.set_at_dyn(index, new_value),
        }
    }
    pub fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        self.value_holder().slice_dyn(start, stop, stride)
    }
    pub fn iter(&self) -> Result<RefIterable, ValueError> {
        let borrowed: ObjectRef<dyn TypedValueDyn> = self.try_value_holder(true).unwrap();
        let mut err = Ok(());
        let typed_into_iter = ObjectRef::map(borrowed, |t| match t.iter_dyn() {
            Ok(r) => r,
            Err(e) => {
                err = Err(e);
                &FakeTypedIterable
            }
        });
        err?;
        Ok(RefIterable::new(typed_into_iter))
    }
    pub fn to_vec(&self) -> Result<Vec<Value>, ValueError> {
        Ok(self.iter()?.to_vec())
    }
    pub fn length(&self) -> Result<i64, ValueError> {
        self.value_holder().length_dyn()
    }
    pub fn get_attr(&self, attribute: &str) -> ValueResult {
        self.value_holder().get_attr_dyn(attribute)
    }
    pub fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        self.value_holder().has_attr_dyn(attribute)
    }
    pub fn set_attr(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        match self.try_value_holder_mut() {
            Err(ObjectBorrowMutError::Immutable) => {
                return Err(ValueError::OperationNotSupported {
                    op: format!(".{} =", attribute),
                    left: self.get_type().to_owned(),
                    right: None,
                });
            }
            Err(e) => Err(e.into()),
            Ok(mut v) => v.set_attr_dyn(attribute, new_value),
        }
    }
    pub fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        self.value_holder().dir_attr_dyn()
    }
    pub fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        self.value_holder().is_in_dyn(other)
    }
    pub fn plus(&self) -> ValueResult {
        self.value_holder().plus_dyn()
    }
    pub fn minus(&self) -> ValueResult {
        self.value_holder().minus_dyn()
    }
    pub fn add(&self, other: Value) -> ValueResult {
        self.value_holder().add_dyn(other)
    }
    pub fn sub(&self, other: Value) -> ValueResult {
        self.value_holder().sub_dyn(other)
    }
    pub fn mul(&self, other: Value) -> ValueResult {
        self.value_holder().mul_dyn(other)
    }
    pub fn percent(&self, other: Value) -> ValueResult {
        self.value_holder().percent_dyn(other)
    }
    pub fn div(&self, other: Value) -> ValueResult {
        self.value_holder().div_dyn(other)
    }
    pub fn floor_div(&self, other: Value) -> ValueResult {
        self.value_holder().floor_div_dyn(other)
    }
    pub fn pipe(&self, other: Value) -> ValueResult {
        self.value_holder().pipe_dyn(other)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{}", self.to_str())
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        self.equals(other) == Ok(true)
    }
}
impl Eq for Value {}

impl Value {
    /// Get a reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed mutably.
    pub fn downcast_ref<T: TypedValue>(&self) -> Option<ObjectRef<T>> {
        let object_ref = self.value_holder();
        let any = ObjectRef::map(object_ref, |o| o.as_any_ref());
        ObjectRef::flat_map(any, |any| any.downcast_ref())
    }

    /// Get a mutable reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed.
    ///
    /// Error is returned if the value is frozen or frozen for iteration.
    pub fn downcast_mut<T: TypedValue<Holder = Mutable<T>>>(
        &self,
    ) -> Result<Option<ObjectRefMut<'_, T>>, ValueError> {
        let object_ref = match self.try_value_holder_mut() {
            Err(e @ ObjectBorrowMutError::Frozen)
            | Err(e @ ObjectBorrowMutError::FrozenForIteration) => return Err(e.into()),
            Err(e) => panic!("already borrowed: {:?}", e),
            Ok(v) => v,
        };
        let any = ObjectRefMut::map(object_ref, |o| o.as_any_mut());
        Ok(ObjectRefMut::flat_map(any, |any| any.downcast_mut()))
    }
}

// Submodules
pub mod boolean;
pub(crate) mod cell;
pub mod context;
pub mod dict;
pub mod error;
pub(crate) mod frozen;
pub mod function;
pub mod hashed_value;
pub(crate) mod inspect;
pub mod int;
pub mod iter;
pub mod list;
pub mod none;
pub mod range;
pub mod slice_indices;
pub mod string;
pub mod tuple;

use crate::stdlib::structs::StarlarkStruct;
use crate::values::cell::error::ObjectBorrowError;
use crate::values::cell::error::ObjectBorrowMutError;
use crate::values::cell::header::ObjectHeader;
use crate::values::cell::ObjectCell;
use crate::values::cell::ObjectRef;
use crate::values::cell::ObjectRefMut;
use crate::values::none::NoneType;

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter;

    #[test]
    fn can_implement_compare() {
        #[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
        struct WrappedNumber(u64);

        /// Define the NoneType type
        impl TypedValue for WrappedNumber {
            fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
                write!(buf, "{:?}", self)
            }
            const TYPE: &'static str = "WrappedNumber";
            fn to_bool(&self) -> bool {
                false
            }
            fn get_hash(&self) -> Result<u64, ValueError> {
                Ok(self.0)
            }
            fn compare(&self, other: &WrappedNumber) -> Result<std::cmp::Ordering, ValueError> {
                Ok(std::cmp::Ord::cmp(self, other))
            }

            type Holder = Immutable<WrappedNumber>;

            fn values_for_descendant_check_and_freeze<'a>(
                &'a self,
            ) -> Box<dyn Iterator<Item = Value> + 'a> {
                Box::new(iter::empty())
            }
        }

        let one = Value::new(WrappedNumber(1));
        let another_one = Value::new(WrappedNumber(1));
        let two = Value::new(WrappedNumber(2));

        use std::cmp::Ordering::*;

        assert_eq!(one.compare(&one), Ok(Equal));
        assert_eq!(one.compare(&another_one), Ok(Equal));
        assert_eq!(one.compare(&two), Ok(Less));
        assert_eq!(two.compare(&one), Ok(Greater));
    }

    #[test]
    fn compare_between_different_types() {
        assert!(Value::new(1).compare(&Value::new(false)).is_err());
    }
}
