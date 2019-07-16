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
//!     fn to_repr(&self) -> String {
//!         "None".to_owned()
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
use std::any::Any;
use std::cell::{RefCell, RefMut};
use std::cmp::Ordering;
use std::fmt;
use std::marker;
use std::rc::Rc;

/// ValueInner wraps the actual value or a memory pointer
/// to the actual value for complex type.
#[derive(Clone)]
enum ValueInner {
    None(ValueHolder<NoneType>),
    Bool(ValueHolder<bool>),
    Int(ValueHolder<i64>),
    Other(Rc<dyn ValueHolderDyn>),
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

    fn value_holder(&self) -> &(dyn ValueHolderDyn + 'static) {
        match &self.0 {
            ValueInner::None(n) => n,
            ValueInner::Int(i) => i,
            ValueInner::Bool(b) => b,
            ValueInner::Other(rc) => &**rc,
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

    /// Determine if the value pointed by other is a descendant of self
    pub fn is_descendant_value(&self, other: &Value) -> bool {
        self.value_holder().is_descendant(other.data_ptr())
    }

    /// Object data pointer.
    pub fn data_ptr(&self) -> DataPtr {
        self.value_holder().data_ptr()
    }

    /// Function id used to detect recursion.
    pub fn function_id(&self) -> FunctionId {
        self.value_holder().function_id()
    }
}

pub trait Mutability {
    type Content: TypedValue;

    /// This type is mutable or immutable.
    const MUTABLE: bool;

    /// Type of cell which contains the object.
    type Cell: RefCellOrImmutable<Content = Self::Content>;

    /// Type of cell which contains mutability flag.
    type MutabilityCell: MutabilityCell;
}

struct ValueHolder<T: TypedValue> {
    mutability: <<T as TypedValue>::Holder as Mutability>::MutabilityCell,
    content: <<T as TypedValue>::Holder as Mutability>::Cell,
}

impl<T: TypedValue> ValueHolder<T> {
    fn new(value: T) -> ValueHolder<T> {
        ValueHolder {
            mutability: <<T as TypedValue>::Holder as Mutability>::MutabilityCell::new(),
            content: <<T as TypedValue>::Holder as Mutability>::Cell::new(value),
        }
    }
}

impl<T: TypedValue<Holder = Immutable<T>> + Clone> Clone for ValueHolder<T> {
    fn clone(&self) -> Self {
        ValueHolder {
            mutability: self.mutability.clone(),
            content: self.content.clone(),
        }
    }
}

/// Type parameter for immutable types.
pub struct Immutable<T>(marker::PhantomData<T>);
/// Type parameter for mutable types.
pub struct Mutable<T>(marker::PhantomData<T>);

impl<T: TypedValue> Mutability for Mutable<T> {
    type Content = T;
    const MUTABLE: bool = true;
    type Cell = RefCell<T>;
    type MutabilityCell = MutableMutability;
}

impl<T: TypedValue> Mutability for Immutable<T> {
    type Content = T;
    const MUTABLE: bool = false;
    type Cell = ImmutableCell<T>;
    type MutabilityCell = ImmutableMutability;
}

/// Pointer to data, used for cycle checks.
#[derive(Copy, Clone, Debug, Eq)]
pub struct DataPtr(*const ());

impl<T: TypedValue> From<*const T> for DataPtr {
    fn from(p: *const T) -> Self {
        DataPtr(p as *const ())
    }
}

impl<T: TypedValue> From<&'_ T> for DataPtr {
    fn from(p: &T) -> Self {
        DataPtr::from(p as *const T)
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

impl<T: TypedValue> ValueHolderDyn for ValueHolder<T> {
    fn as_any_mut(&self) -> Result<Option<RefMut<'_, dyn Any>>, ValueError> {
        self.mutability.get().test()?;
        Ok(if T::Holder::MUTABLE {
            Some(RefMut::map(self.content.borrow_mut(), |v| {
                v as &mut dyn Any
            }))
        } else {
            None
        })
    }

    fn as_any_ref(&self) -> RefOrRef<'_, dyn Any> {
        RefOrRef::map(self.content.borrow(), |v| v as &dyn Any)
    }

    fn data_ptr(&self) -> DataPtr {
        DataPtr::from(self.content.as_ptr())
    }

    fn function_id(&self) -> FunctionId {
        self.content
            .borrow()
            .function_id()
            .unwrap_or(FunctionId(self.data_ptr()))
    }

    /// Freezes the current value.
    fn freeze(&self) {
        self.mutability.freeze();
        for mut value in self
            .content
            .borrow()
            .values_for_descendant_check_and_freeze()
        {
            value.freeze();
        }
    }

    /// Freezes the current value for iterating over.
    fn freeze_for_iteration(&self) {
        self.mutability.freeze_for_iteration();
    }

    /// Unfreezes the current value for iterating over.
    fn unfreeze_for_iteration(&self) {
        self.mutability.unfreeze_for_iteration();
    }

    fn to_str(&self) -> String {
        self.content.borrow().to_str()
    }

    fn to_repr(&self) -> String {
        self.content.borrow().to_repr()
    }

    fn get_type(&self) -> &'static str {
        T::TYPE
    }

    fn to_bool(&self) -> bool {
        self.content.borrow().to_bool()
    }

    fn to_int(&self) -> Result<i64, ValueError> {
        self.content.borrow().to_int()
    }

    fn get_hash(&self) -> Result<u64, ValueError> {
        self.content.borrow().get_hash()
    }

    fn is_descendant(&self, other: DataPtr) -> bool {
        if self.data_ptr() == other {
            return true;
        }
        if let Ok(borrow) = self.content.try_borrow() {
            borrow
                .values_for_descendant_check_and_freeze()
                .any(|x| x.is_descendant(other))
        } else {
            // We have already borrowed mutably this value,
            // which means we are trying to mutate it, assigning other to it.
            true
        }
    }

    fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        let _stack_depth_guard = call_stack::try_inc()?;

        match other.downcast_ref::<T>() {
            Some(other) => self.content.borrow().equals(&*other),
            None => Ok(false),
        }
    }

    fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        let _stack_depth_guard = call_stack::try_inc()?;

        match other.downcast_ref::<T>() {
            Some(other) => self.content.borrow().compare(&*other),
            None => Err(ValueError::OperationNotSupported {
                op: "compare".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()),
            }),
        }
    }

    fn call(
        &self,
        call_stack: &CallStack,
        type_values: TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        self.content
            .borrow()
            .call(call_stack, type_values, positional, named, args, kwargs)
    }

    fn at(&self, index: Value) -> Result<Value, ValueError> {
        self.content.borrow().at(index)
    }

    fn set_at(&self, index: Value, new_value: Value) -> Result<(), ValueError> {
        // must explicitly check for mutability, otherwise `borrow_mut` below will fail
        if !T::Holder::MUTABLE {
            return Err(ValueError::OperationNotSupported {
                op: "[] =".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(index.get_type().to_owned()),
            });
        }
        self.mutability.get().test()?;
        self.content.borrow_mut().set_at(index, new_value)
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<Value, ValueError> {
        self.content.borrow().slice(start, stop, stride)
    }

    fn iter<'a>(&'a self) -> Result<RefIterable<'a>, ValueError> {
        let borrowed: RefOrRef<'_, T> = self.content.borrow();
        let mut err = Ok(());
        let typed_into_iter = RefOrRef::map(borrowed, |t| match t.iter() {
            Ok(r) => r,
            Err(e) => {
                err = Err(e);
                &FakeTypedIterable
            }
        });
        err?;
        Ok(RefIterable::new(typed_into_iter))
    }

    fn length(&self) -> Result<i64, ValueError> {
        self.content.borrow().length()
    }

    fn get_attr(&self, attribute: &str) -> Result<Value, ValueError> {
        self.content.borrow().get_attr(attribute)
    }

    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        self.content.borrow().has_attr(attribute)
    }

    fn set_attr(&self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        // must explicitly check for mutability, otherwise `borrow_mut` below will fail
        if !T::Holder::MUTABLE {
            return Err(ValueError::OperationNotSupported {
                op: format!(".{} =", attribute),
                left: self.get_type().to_owned(),
                right: None,
            });
        }
        self.mutability.get().test()?;
        self.content.borrow_mut().set_attr(attribute, new_value)
    }

    fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        self.content.borrow().dir_attr()
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        self.content.borrow().is_in(other)
    }

    fn plus(&self) -> Result<Value, ValueError> {
        self.content.borrow().plus().map(Value::new)
    }

    fn minus(&self) -> Result<Value, ValueError> {
        self.content.borrow().minus().map(Value::new)
    }

    fn add(&self, other: Value) -> Result<Value, ValueError> {
        match other.downcast_ref::<T>() {
            Some(other) => self.content.borrow().add(&*other).map(Value::new),
            None => Err(ValueError::IncorrectParameterType),
        }
    }

    fn sub(&self, other: Value) -> Result<Value, ValueError> {
        match other.downcast_ref() {
            Some(other) => self.content.borrow().sub(&*other).map(Value::new),
            None => Err(ValueError::IncorrectParameterType),
        }
    }

    fn mul(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().mul(other)
    }

    fn percent(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().percent(other)
    }

    fn div(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().div(other)
    }

    fn floor_div(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().floor_div(other)
    }

    fn pipe(&self, other: Value) -> Result<Value, ValueError> {
        self.content.borrow().pipe(other)
    }
}

/// `ValueHolder` as virtual functions to put into `Value`.
/// Should not be used or implemented directly.
trait ValueHolderDyn {
    /// This function panics is value is borrowed,
    /// `None` is returned for immutable types,
    /// and `Err` is returned when value is locked for iteration or frozen.
    fn as_any_mut(&self) -> Result<Option<RefMut<'_, dyn Any>>, ValueError>;

    /// This function panics if value is mutably borrowed.
    fn as_any_ref(&self) -> RefOrRef<'_, dyn Any>;

    /// Pointer to `TypedValue` object, used for cycle checks.
    fn data_ptr(&self) -> DataPtr;

    /// Id used to detect recursion (which is prohibited in Starlark)
    fn function_id(&self) -> FunctionId;

    fn freeze(&self);

    fn freeze_for_iteration(&self);

    fn unfreeze_for_iteration(&self);

    fn to_str(&self) -> String;

    fn to_repr(&self) -> String;

    fn get_type(&self) -> &'static str;

    fn to_bool(&self) -> bool;

    fn to_int(&self) -> Result<i64, ValueError>;

    fn get_hash(&self) -> Result<u64, ValueError>;

    fn is_descendant(&self, other: DataPtr) -> bool;

    fn equals(&self, other: &Value) -> Result<bool, ValueError>;
    fn compare(&self, other: &Value) -> Result<Ordering, ValueError>;

    fn call(
        &self,
        call_stack: &CallStack,
        type_values: TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult;

    fn at(&self, index: Value) -> ValueResult;

    fn set_at(&self, index: Value, _new_value: Value) -> Result<(), ValueError>;
    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult;

    fn iter<'a>(&'a self) -> Result<RefIterable<'a>, ValueError>;

    fn length(&self) -> Result<i64, ValueError>;

    fn get_attr(&self, attribute: &str) -> ValueResult;

    fn has_attr(&self, _attribute: &str) -> Result<bool, ValueError>;

    fn set_attr(&self, attribute: &str, _new_value: Value) -> Result<(), ValueError>;

    fn dir_attr(&self) -> Result<Vec<String>, ValueError>;

    fn is_in(&self, other: &Value) -> Result<bool, ValueError>;

    fn plus(&self) -> ValueResult;

    fn minus(&self) -> ValueResult;

    fn add(&self, other: Value) -> ValueResult;

    fn sub(&self, other: Value) -> ValueResult;

    fn mul(&self, other: Value) -> ValueResult;

    fn percent(&self, other: Value) -> ValueResult;

    fn div(&self, other: Value) -> ValueResult;

    fn floor_div(&self, other: Value) -> ValueResult;

    fn pipe(&self, other: Value) -> ValueResult;
}

/// A trait for a value with a type that all variable container
/// will implement.
pub trait TypedValue: Sized + 'static {
    /// Must be either `MutableHolder<Self>` or `ImmutableHolder<Self>`
    type Holder: Mutability<Content = Self>;

    /// Return a string describing the type of self, as returned by the type() function.
    const TYPE: &'static str;

    /// Create a value for `TypedValue`.
    ///
    /// This function should be overridden only by builtin types.
    #[doc(hidden)]
    fn new_value(self) -> Value {
        Value(ValueInner::Other(Rc::new(ValueHolder::new(self))))
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
        self.to_repr()
    }

    /// Return a string representation of self, as returned by the repr() function.
    fn to_repr(&self) -> String {
        format!("<{}>", Self::TYPE)
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
        _call_stack: &CallStack,
        _type_values: TypeValues,
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
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Value[{}]({})", self.get_type(), self.to_repr())
    }
}

impl Value {
    pub fn freeze(&mut self) {
        self.value_holder().freeze()
    }
    pub fn freeze_for_iteration(&mut self) {
        self.value_holder().freeze_for_iteration()
    }
    pub fn unfreeze_for_iteration(&mut self) {
        self.value_holder().unfreeze_for_iteration()
    }
    pub fn to_str(&self) -> String {
        self.value_holder().to_str()
    }
    pub fn to_repr(&self) -> String {
        self.value_holder().to_repr()
    }
    pub fn get_type(&self) -> &'static str {
        self.value_holder().get_type()
    }
    pub fn to_bool(&self) -> bool {
        self.value_holder().to_bool()
    }
    pub fn to_int(&self) -> Result<i64, ValueError> {
        self.value_holder().to_int()
    }
    pub fn get_hash(&self) -> Result<u64, ValueError> {
        self.value_holder().get_hash()
    }
    pub fn equals(&self, other: &Value) -> Result<bool, ValueError> {
        self.value_holder().equals(other)
    }
    pub fn compare(&self, other: &Value) -> Result<Ordering, ValueError> {
        self.value_holder().compare(other)
    }

    pub fn is_descendant(&self, other: DataPtr) -> bool {
        self.value_holder().is_descendant(other)
    }

    pub fn call(
        &self,
        call_stack: &CallStack,
        type_values: TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        self.value_holder()
            .call(call_stack, type_values, positional, named, args, kwargs)
    }

    pub fn at(&self, index: Value) -> ValueResult {
        self.value_holder().at(index)
    }

    pub fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        self.value_holder().set_at(index, new_value)
    }
    pub fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        self.value_holder().slice(start, stop, stride)
    }
    pub fn iter<'a>(&'a self) -> Result<RefIterable<'a>, ValueError> {
        self.value_holder().iter()
    }
    pub fn to_vec(&self) -> Result<Vec<Value>, ValueError> {
        Ok(self.iter()?.to_vec())
    }
    pub fn length(&self) -> Result<i64, ValueError> {
        self.value_holder().length()
    }
    pub fn get_attr(&self, attribute: &str) -> ValueResult {
        self.value_holder().get_attr(attribute)
    }
    pub fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        self.value_holder().has_attr(attribute)
    }
    pub fn set_attr(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        self.value_holder().set_attr(attribute, new_value)
    }
    pub fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        self.value_holder().dir_attr()
    }
    pub fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        self.value_holder().is_in(other)
    }
    pub fn plus(&self) -> ValueResult {
        self.value_holder().plus()
    }
    pub fn minus(&self) -> ValueResult {
        self.value_holder().minus()
    }
    pub fn add(&self, other: Value) -> ValueResult {
        self.value_holder().add(other)
    }
    pub fn sub(&self, other: Value) -> ValueResult {
        self.value_holder().sub(other)
    }
    pub fn mul(&self, other: Value) -> ValueResult {
        self.value_holder().mul(other)
    }
    pub fn percent(&self, other: Value) -> ValueResult {
        self.value_holder().percent(other)
    }
    pub fn div(&self, other: Value) -> ValueResult {
        self.value_holder().div(other)
    }
    pub fn floor_div(&self, other: Value) -> ValueResult {
        self.value_holder().floor_div(other)
    }
    pub fn pipe(&self, other: Value) -> ValueResult {
        self.value_holder().pipe(other)
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

impl dyn ValueHolderDyn {
    // To be calleds by convert_slice_indices only
    fn convert_index_aux(
        len: i64,
        v1: Option<Value>,
        default: i64,
        min: i64,
        max: i64,
    ) -> Result<i64, ValueError> {
        if let Some(v) = v1 {
            if v.get_type() == "NoneType" {
                Ok(default)
            } else {
                match v.to_int() {
                    Ok(x) => {
                        let i = if x < 0 { len + x } else { x };
                        if i < min {
                            Ok(min)
                        } else if i > max {
                            Ok(max)
                        } else {
                            Ok(i)
                        }
                    }
                    Err(..) => Err(ValueError::IncorrectParameterType),
                }
            }
        } else {
            Ok(default)
        }
    }

    /// Macro to parse the index for at/set_at methods.
    ///
    /// Return an `i64` from self corresponding to the index recenterd between 0 and len.
    /// Raise the correct errors if the value is not numeric or the index is out of bound.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # assert!(
    /// Value::new(6).convert_index(7).unwrap() == 6
    /// # );
    /// # assert!(
    /// Value::new(-1).convert_index(7).unwrap() == 6
    /// # );
    /// ```
    ///
    /// The following examples would return an error
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::error::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// Value::from("a").convert_index(7) == Err(ValueError::IncorrectParameterType)
    /// # );
    /// # assert!(
    /// Value::new(8).convert_index(7) == Err(ValueError::IndexOutOfBound(8))   // 8 > 7 = len
    /// # );
    /// # assert!(
    /// Value::new(-8).convert_index(7) == Err(ValueError::IndexOutOfBound(-1)) // -8 + 7 = -1 < 0
    /// # );
    /// ```
    pub fn convert_index(&self, len: i64) -> Result<i64, ValueError> {
        match self.to_int() {
            Ok(x) => {
                let i = if x < 0 {
                    len.checked_add(x).ok_or(ValueError::IntegerOverflow)?
                } else {
                    x
                };
                if i < 0 || i >= len {
                    Err(ValueError::IndexOutOfBound(i))
                } else {
                    Ok(i)
                }
            }
            Err(..) => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl Value {
    /// Parse indices for slicing.
    ///
    /// Takes the object length and 3 optional values and returns `(i64, i64, i64)`
    /// with those index correctly converted in range of length.
    /// Return the correct errors if the values are not numeric or the stride is 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// let six      = Some(Value::new(6));
    /// let minusone = Some(Value::new(-1));
    /// let ten      = Some(Value::new(10));
    ///
    /// # assert!(
    /// Value::convert_slice_indices(7, six, None, None).unwrap() == (6, 7, 1)
    /// # );
    /// # assert!(
    /// Value::convert_slice_indices(7, minusone.clone(), None, minusone.clone()).unwrap()
    ///        == (6, -1, -1)
    /// # );
    /// # assert!(
    /// Value::convert_slice_indices(7, minusone, ten, None).unwrap() == (6, 7, 1)
    /// # );
    /// ```
    pub fn convert_slice_indices(
        len: i64,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<(i64, i64, i64), ValueError> {
        let stride = stride.unwrap_or_else(|| Value::new(1));
        let stride = if stride.get_type() == "NoneType" {
            Ok(1)
        } else {
            stride.to_int()
        };
        match stride {
            Ok(0) => Err(ValueError::IndexOutOfBound(0)),
            Ok(stride) => {
                let def_start = if stride < 0 { len - 1 } else { 0 };
                let def_end = if stride < 0 { -1 } else { len };
                let clamp = if stride < 0 { -1 } else { 0 };
                let start =
                    ValueHolderDyn::convert_index_aux(len, start, def_start, clamp, len + clamp);
                let stop =
                    ValueHolderDyn::convert_index_aux(len, stop, def_end, clamp, len + clamp);
                match (start, stop) {
                    (Ok(s1), Ok(s2)) => Ok((s1, s2, stride)),
                    (Err(x), ..) => Err(x),
                    (Ok(..), Err(x)) => Err(x),
                }
            }
            _ => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl Value {
    /// Get a reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed mutably.
    pub fn downcast_ref<T: TypedValue>(&self) -> Option<RefOrRef<'_, T>> {
        let any = self.value_holder().as_any_ref();
        if any.is::<T>() {
            Some(RefOrRef::map(any, |any| any.downcast_ref().unwrap()))
        } else {
            None
        }
    }

    /// Get a mutable reference to underlying data or `None`
    /// if contained object has different type than requested.
    ///
    /// This function panics if the `Value` is borrowed.
    ///
    /// Error is returned if the value is frozen or frozen for iteration.
    pub fn downcast_mut<T: TypedValue<Holder = Mutable<T>>>(
        &self,
    ) -> Result<Option<RefMut<'_, T>>, ValueError> {
        let any = match self.value_holder().as_any_mut()? {
            Some(any) => any,
            None => return Ok(None),
        };
        Ok(if any.is::<T>() {
            Some(RefMut::map(any, |any| any.downcast_mut().unwrap()))
        } else {
            None
        })
    }

    pub fn convert_index(&self, len: i64) -> Result<i64, ValueError> {
        self.value_holder().convert_index(len)
    }
}

// Submodules
pub mod boolean;
pub mod dict;
pub mod error;
pub mod function;
pub mod hashed_value;
pub mod int;
pub mod iter;
pub mod list;
pub mod mutability;
pub mod none;
pub mod range;
pub mod string;
pub mod tuple;

use crate::values::mutability::{
    ImmutableCell, ImmutableMutability, MutabilityCell, MutableMutability, RefCellOrImmutable,
    RefOrRef,
};
use crate::values::none::NoneType;

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter;

    #[test]
    fn test_convert_index() {
        assert_eq!(Ok(6), Value::new(6).convert_index(7));
        assert_eq!(Ok(6), Value::new(-1).convert_index(7));
        assert_eq!(
            Ok((6, 7, 1)),
            Value::convert_slice_indices(7, Some(Value::new(6)), None, None)
        );
        assert_eq!(
            Ok((6, -1, -1)),
            Value::convert_slice_indices(7, Some(Value::new(-1)), None, Some(Value::new(-1)))
        );
        assert_eq!(
            Ok((6, 7, 1)),
            Value::convert_slice_indices(7, Some(Value::new(-1)), Some(Value::new(10)), None)
        );
        // Errors
        assert_eq!(
            Err(ValueError::IncorrectParameterType),
            Value::from("a").convert_index(7)
        );
        assert_eq!(
            Err(ValueError::IndexOutOfBound(8)),
            Value::new(8).convert_index(7)
        );
        assert_eq!(
            Err(ValueError::IndexOutOfBound(-1)),
            Value::new(-8).convert_index(7)
        );
    }

    #[test]
    fn can_implement_compare() {
        #[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
        struct WrappedNumber(u64);

        /// Define the NoneType type
        impl TypedValue for WrappedNumber {
            fn to_repr(&self) -> String {
                format!("{:?}", self)
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
