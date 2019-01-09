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
//! Defining a new Starlark type can be done by implenting the [TypedValue](trait.TypedValue.html)
//! trait. All method of that trait are operation needed by Starlark interpreter to understand the
//! type. The [not_supported!](macro.not_supported.html) macro let us tell which operation is not
//! supported by the current type.
//!
//! For example the `NoneType` trait implementation is the following:
//!
//! ```rust,ignore
//! /// Define the NoneType type
//! impl TypedValue for Option<()> {
//!     immutable!();
//!     any!();  // Generally you don't want to implement as_any() and as_any_mut() yourself.
//!     fn to_str(&self) -> String {
//!         "None".to_owned()
//!     }
//!     fn to_repr(&self) -> String {
//!         self.to_str()
//!     }
//!     not_supported!(to_int);
//!     fn get_type(&self) -> &'static str {
//!         "NoneType"
//!     }
//!     fn to_bool(&self) -> bool {
//!         false
//!     }
//!     // just took the result of hash(None) in macos python 2.7.10 interpreter.
//!     fn get_hash(&self) -> Result<u64, ValueError> {
//!         Ok(9223380832852120682)
//!     }
//!     fn compare(&self, other: &Value) -> Ordering { default_compare(self, other) }
//!     not_supported!(binop);
//!     not_supported!(container);
//!     not_supported!(function);
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
use codemap::Span;
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use environment::Environment;
use linked_hash_map::LinkedHashMap;
use std::any::Any;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;
use syntax::errors::SyntaxError;

// TODO: move that code in some common error code list?
// CV prefix = Critical Value expression
pub const NOT_SUPPORTED_ERROR_CODE: &str = "CV00";
pub const IMMUTABLE_ERROR_CODE: &str = "CV01";
pub const INCORRECT_PARAMETER_TYPE_ERROR_CODE: &str = "CV02";
pub const OUT_OF_BOUND_ERROR_CODE: &str = "CV03";
pub const NOT_HASHABLE_VALUE_ERROR_CODE: &str = "CV04";
pub const KEY_NOT_FOUND_ERROR_CODE: &str = "CV05";
pub const INTERPOLATION_FORMAT_ERROR_CODE: &str = "CV06";
pub const INTERPOLATION_OUT_OF_UTF8_RANGE_ERROR_CODE: &str = "CV07";
pub const DIVISION_BY_ZERO_ERROR_CODE: &str = "CV08";
pub const INTERPOLATION_TOO_MANY_PARAMS_ERROR_CODE: &str = "CV09";
pub const INTERPOLATION_NOT_ENOUGH_PARAMS_ERROR_CODE: &str = "CV10";
pub const INTERPOLATION_VALUE_IS_NOT_CHAR_ERROR_CODE: &str = "CV12";
pub const TOO_MANY_RECURSION_LEVEL_ERROR_CODE: &str = "CV13";
pub const UNSUPPORTED_RECURSIVE_DATA_STRUCTURE_ERROR_CODE: &str = "CV14";
pub const CANNOT_MUTATE_DURING_ITERATION_ERROR_CODE: &str = "CV15";

// Maximum recursion level for comparison
// TODO(dmarting): those are rather short, maybe make it configurable?
#[cfg(debug_assertions)]
const MAX_RECURSION: u32 = 200;

#[cfg(not(debug_assertions))]
const MAX_RECURSION: u32 = 3000;

/// Error that can be returned by function from the `TypedValue` trait,
#[derive(Clone, Debug)]
pub enum ValueError {
    /// The operation is not supported for this type.
    OperationNotSupported {
        op: String,
        left: String,
        right: Option<String>,
    },
    /// The operation is not supported for this type because type is not of a certain category.
    TypeNotX {
        object_type: String,
        op: String,
    },
    /// Division by 0
    DivisionByZero,
    /// Trying to modify an immutable value.
    CannotMutateImmutableValue,
    /// Trying to apply incorrect parameter type, e.g. for slicing.
    IncorrectParameterType,
    /// Trying to access an index outside of the value range,
    IndexOutOfBound(i64),
    /// The value is not hashable but was requested for a hash structure (e.g. dictionary).
    NotHashableValue,
    /// The key was not found in the collection
    KeyNotFound(Value),
    /// Wrapper around runtime errors to be bubbled up.
    Runtime(RuntimeError),
    /// Wrapper around diagnosed errors to be bubbled up.
    DiagnosedError(Diagnostic),
    /// Format of the interpolation string is incorrect.
    InterpolationFormat,
    /// Trying to interpolate with %c an integer that is not in the UTF-8 range.
    InterpolationValueNotInUTFRange(u32),
    /// Interpolation parameter is too big for the format string.
    TooManyParametersForInterpolation,
    /// Interpolation parameter is too small for the format string.
    NotEnoughParametersForInterpolation,
    InterpolationValueNotChar,
    /// Too many recursion in internal operation
    TooManyRecursionLevel,
    /// Recursive data structure are not allowed because they would allow infinite loop.
    UnsupportedRecursiveDataStructure,
    /// It is not allowed to mutate a structure during iteration.
    MutationDuringIteration,
}

/// A simpler error format to return as a ValueError
#[derive(Clone, Debug)]
pub struct RuntimeError {
    pub code: &'static str,
    pub message: String,
    pub label: String,
}

impl<T: Into<RuntimeError>> SyntaxError for T {
    fn to_diagnostic(self, file_span: Span) -> Diagnostic {
        ValueError::Runtime(self.into()).to_diagnostic(file_span)
    }
}

impl Into<ValueError> for RuntimeError {
    fn into(self) -> ValueError {
        ValueError::Runtime(self)
    }
}

impl SyntaxError for ValueError {
    fn to_diagnostic(self, file_span: Span) -> Diagnostic {
        match self {
            ValueError::DiagnosedError(d) => d,
            _ => {
                let sl = SpanLabel {
                    span: file_span,
                    style: SpanStyle::Primary,
                    label: Some(match self {
                        ValueError::Runtime(ref e) => e.label.clone(),
                        ValueError::OperationNotSupported {
                            ref op,
                            ref left,
                            right: Some(ref right),
                        } => format!("{} not supported for types {} and {}", op, left, right),
                        ValueError::OperationNotSupported {
                            ref op,
                            ref left,
                            right: None,
                        } => format!("{} not supported for type {}", op, left),
                        ValueError::TypeNotX {
                            ref object_type,
                            ref op,
                        } => format!("The type '{}' is not {}", object_type, op),
                        ValueError::DivisionByZero => "Division by zero".to_owned(),
                        ValueError::CannotMutateImmutableValue => "Immutable".to_owned(),
                        ValueError::IncorrectParameterType => {
                            "Type of parameters mismatch".to_owned()
                        }
                        ValueError::IndexOutOfBound(..) => "Index out of bound".to_owned(),
                        ValueError::NotHashableValue => "Value is not hashable".to_owned(),
                        ValueError::KeyNotFound(..) => "Key not found".to_owned(),
                        ValueError::InterpolationFormat => {
                            "Interpolation string format incorrect".to_owned()
                        }
                        ValueError::InterpolationValueNotInUTFRange(ref c) => {
                            format!("Invalid codepoint 0x{:x}", c)
                        }
                        ValueError::TooManyParametersForInterpolation => {
                            "Too many arguments for format string".to_owned()
                        }
                        ValueError::NotEnoughParametersForInterpolation => {
                            "Not enough arguments for format string".to_owned()
                        }
                        ValueError::InterpolationValueNotChar => {
                            "'%c' formatter requires a single-character string".to_owned()
                        }
                        ValueError::TooManyRecursionLevel => "Too many recursion".to_owned(),
                        ValueError::UnsupportedRecursiveDataStructure => {
                            "Unsupported recursive data structure".to_owned()
                        }
                        ValueError::MutationDuringIteration => {
                            "Cannot mutate an iterable while iterating".to_owned()
                        }
                        _ => unreachable!(),
                    }),
                };
                Diagnostic {
                    level: Level::Error,
                    message: match self {
                        ValueError::Runtime(ref e) => e.message.clone(),
                        ValueError::OperationNotSupported {
                            ref op,
                            ref left,
                            right: Some(ref right),
                        } => format!("Cannot {} types {} and {}", op, left, right),
                        ValueError::OperationNotSupported {
                            ref op,
                            ref left,
                            right: None,
                        } => format!("Cannot {} on type {}", op, left),
                        ValueError::TypeNotX {
                            ref object_type,
                            ref op,
                        } => format!("The type '{}' is not {}", object_type, op),
                        ValueError::DivisionByZero => "Cannot divide by zero".to_owned(),
                        ValueError::CannotMutateImmutableValue => "Immutable".to_owned(),
                        ValueError::IncorrectParameterType => {
                            "Type of parameters mismatch".to_owned()
                        }
                        ValueError::IndexOutOfBound(ref b) => {
                            format!("Index {} is out of bound", b)
                        }
                        ValueError::NotHashableValue => "Value is not hashable".to_owned(),
                        ValueError::KeyNotFound(ref k) => format!("Key '{}' was not found", k),
                        ValueError::InterpolationFormat => concat!(
                            "Interpolation string format is incorrect:",
                            " '%' must be followed by an optional name and a specifier ",
                            "('s', 'r', 'd', 'i', 'o', 'x', 'X', 'c')"
                        ).to_owned(),
                        ValueError::InterpolationValueNotInUTFRange(ref c) => format!(
                            concat!(
                                "Value 0x{:x} passed for %c formattter is not a valid",
                                " UTF-8 codepoint"
                            ),
                            c
                        ),
                        ValueError::TooManyParametersForInterpolation => {
                            "Too many arguments for format string".to_owned()
                        }
                        ValueError::NotEnoughParametersForInterpolation => {
                            "Not enough arguments for format string".to_owned()
                        }
                        ValueError::InterpolationValueNotChar => {
                            "'%c' formatter requires a single-character string".to_owned()
                        }
                        ValueError::TooManyRecursionLevel => "Too many recursion levels".to_owned(),
                        ValueError::UnsupportedRecursiveDataStructure => concat!(
                            "This operation create a recursive data structure. Recursive data",
                            "structure are disallowed because infinite loops are disallowed in Starlark."
                        ).to_owned(),
                        ValueError::MutationDuringIteration => {
                            "This operation mutate an iterable for an iterator is borrowed.".to_owned()
                        }
                        _ => unreachable!(),
                    },
                    code: Some(
                        match self {
                            ValueError::OperationNotSupported { .. } => NOT_SUPPORTED_ERROR_CODE,
                            ValueError::TypeNotX { .. } => NOT_SUPPORTED_ERROR_CODE,
                            ValueError::DivisionByZero => DIVISION_BY_ZERO_ERROR_CODE,
                            ValueError::CannotMutateImmutableValue => IMMUTABLE_ERROR_CODE,
                            ValueError::IncorrectParameterType => {
                                INCORRECT_PARAMETER_TYPE_ERROR_CODE
                            }
                            ValueError::IndexOutOfBound(..) => OUT_OF_BOUND_ERROR_CODE,
                            ValueError::NotHashableValue => NOT_HASHABLE_VALUE_ERROR_CODE,
                            ValueError::KeyNotFound(..) => KEY_NOT_FOUND_ERROR_CODE,
                            ValueError::Runtime(e) => e.code,
                            ValueError::InterpolationFormat => INTERPOLATION_FORMAT_ERROR_CODE,
                            ValueError::InterpolationValueNotInUTFRange(..) => {
                                INTERPOLATION_OUT_OF_UTF8_RANGE_ERROR_CODE
                            }
                            ValueError::TooManyParametersForInterpolation => {
                                INTERPOLATION_TOO_MANY_PARAMS_ERROR_CODE
                            }
                            ValueError::NotEnoughParametersForInterpolation => {
                                INTERPOLATION_NOT_ENOUGH_PARAMS_ERROR_CODE
                            }
                            ValueError::InterpolationValueNotChar => {
                                INTERPOLATION_VALUE_IS_NOT_CHAR_ERROR_CODE
                            }
                            ValueError::TooManyRecursionLevel => {
                                TOO_MANY_RECURSION_LEVEL_ERROR_CODE
                            }
                            ValueError::UnsupportedRecursiveDataStructure => {
                                UNSUPPORTED_RECURSIVE_DATA_STRUCTURE_ERROR_CODE
                            }
                            ValueError::MutationDuringIteration => {
                                CANNOT_MUTATE_DURING_ITERATION_ERROR_CODE
                            }
                            ValueError::DiagnosedError(..) => "U999", // Unknown error
                        }.to_owned(),
                    ),
                    spans: vec![sl],
                }
            }
        }
    }
}

impl PartialEq for ValueError {
    fn eq(&self, other: &ValueError) -> bool {
        match (self, other) {
            (&ValueError::CannotMutateImmutableValue, &ValueError::CannotMutateImmutableValue)
            | (&ValueError::IncorrectParameterType, &ValueError::IncorrectParameterType) => true,
            (
                &ValueError::OperationNotSupported { op: ref x, .. },
                &ValueError::OperationNotSupported { op: ref y, .. },
            ) if x == y => true,
            (&ValueError::IndexOutOfBound(x), &ValueError::IndexOutOfBound(y)) if x == y => true,
            _ => false,
        }
    }
}

/// A value in Starlark.
///
/// This is a wrapper around a [TypedValue] which is cheap to clone and safe to pass around.
#[derive(Clone)]
pub struct Value(pub Rc<RefCell<TypedValue>>);

pub type ValueResult = Result<Value, ValueError>;

impl Value {
    /// Create a new `Value` from a static value.
    pub fn new<T: 'static + TypedValue>(t: T) -> Value {
        Value(Rc::new(RefCell::new(t)))
    }

    /// Clone for inserting into the other container, using weak reference if we do a
    /// recursive insertion.
    pub fn clone_for_container(&self, other: &TypedValue) -> Result<Value, ValueError> {
        if self.is_descendant(other) {
            Err(ValueError::UnsupportedRecursiveDataStructure)
        } else {
            Ok(self.clone())
        }
    }

    pub fn clone_for_container_value(&self, other: &Value) -> Result<Value, ValueError> {
        if self.is_descendant(other.0.borrow().deref()) {
            Err(ValueError::UnsupportedRecursiveDataStructure)
        } else {
            Ok(self.clone())
        }
    }

    /// Determine if the value pointed by other is a descendant of self
    pub fn is_descendant_value(&self, other: &Value) -> bool {
        let borrowed = other.0.borrow();
        self.is_descendant(borrowed.deref())
    }

    /// Return true if other is pointing to the same value as self
    pub fn same_as(&self, other: &TypedValue) -> bool {
        // We use raw pointers..
        let p: *const TypedValue = other;
        let p1: *const TypedValue = self.0.as_ptr();
        p1 == p
    }
}

/// A trait for a value with a type that all variable container
/// will implement.
pub trait TypedValue {
    /// Return true if the value is immutable.
    fn immutable(&self) -> bool;

    /// Convert to an Any. This allows for operation on the native type.
    /// You most certainly don't want to implement it yourself but rather use the `any!` macro.
    fn as_any(&self) -> &Any;

    /// Convert to a mutable Any. This allows for operation on the native type.
    /// You most certainly don't want to implement it yourself but rather use the `any!` macro.
    fn as_any_mut(&mut self) -> &mut Any;

    /// Freeze, i.e. make the value immutable.
    fn freeze(&mut self);

    /// Freeze for interation, i.e. make the value temporary immutable. This does not
    /// propage to child element commpared to the freeze() function.
    fn freeze_for_iteration(&mut self);

    /// Unfreeze after a call to freeze_for_iteration(), i.e. make the value mutable
    /// again.
    fn unfreeze_for_iteration(&mut self);

    /// Return a string describing of self, as returned by the str() function.
    fn to_str(&self) -> String;

    /// Return a string representation of self, as returned by the repr() function.
    fn to_repr(&self) -> String;

    /// Return a string describing the type of self, as returned by the type() function.
    fn get_type(&self) -> &'static str;

    /// Convert self to a Boolean truth value, as returned by the bool() function.
    fn to_bool(&self) -> bool;

    /// Convert self to a integer value, as returned by the int() function if the type is numeric
    /// (not for string).
    fn to_int(&self) -> Result<i64, ValueError>;

    /// Return a hash code for self, as returned by the hash() function, or
    /// OperationNotSupported if there is no hash for this value (e.g. list).
    fn get_hash(&self) -> Result<u64, ValueError>;

    /// Returns true if `other` is a descendent of the current value, used for sanity checks.
    fn is_descendant(&self, other: &TypedValue) -> bool;

    /// Compare `self` with `other`.
    ///
    /// This method returns a result of type
    /// [Ordering](https://doc.rust-lang.org/std/cmp/enum.Ordering.html). If it cannot perform
    /// the comparison it should return `self.get_type().cmp(other.get_type())`.
    ///
    /// This assumption work since we consider that `a < b <=> b > a`.
    ///
    /// __Note__: This does not use the
    ///       (PartialOrd)[https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html] trait as
    ///       the trait needs to know the actual type of the value we compare.
    ///
    /// The extraneous recursion parameter is used to detect deep recursion.
    fn compare(&self, other: &TypedValue, recursion: u32) -> Result<Ordering, ValueError>;

    /// Perform a call on the object, only meaningfull for function object.
    ///
    /// For instance, if this object is a callable (i.e. a function or a method) that adds 2
    /// integers then `self.call(vec![Value::new(1), Value::new(2)], HashMap::new(),
    /// None, None)` would return `Ok(Value::new(3))`.
    ///
    /// # Parameters
    ///
    /// * call_stack: the calling stack, to detect recursion
    /// * env: the environment for the call.
    /// * positional: the list of arguments passed positionally.
    /// * named: the list of argument that were named.
    /// * args: if provided, the `*args` argument.
    /// * kwargs: if provided, the `**kwargs` argument.
    fn call(
        &self,
        call_stack: &[(String, String)],
        env: Environment,
        positional: Vec<Value>,
        named: HashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult;

    /// Perform an array or dictionary indirection.
    ///
    /// This returns the result of `a[index]` if `a` is indexable.
    fn at(&self, index: Value) -> ValueResult;

    /// Set the value at `index` with `new_value`.
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue` if the value was
    /// frozen (but with `ValueError::OperationNotSupported` if the operation is not supported
    /// on this value, even if the value is immutable, e.g. for numbers).
    fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError>;

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
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult;

    /// Returns an iterator over the value of this container if this value hold an iterable
    /// container.
    fn iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError>;

    /// Returns the length of the value, if this value is a sequence.
    fn length(&self) -> Result<i64, ValueError>;

    /// Get an attribute for the current value as would be returned by dotted expression (i.e.
    /// `a.attribute`).
    ///
    /// __Note__: this does not handle native methods which are handled through universe.
    fn get_attr(&self, attribute: &str) -> ValueResult;

    /// Return true if an attribute of name `attribute` exists for the current value.
    ///
    /// __Note__: this does not handle native methods which are handled through universe.
    fn has_attr(&self, attribute: &str) -> Result<bool, ValueError>;

    /// Set the attribute named `attribute` of the current value to `new_value` (e.g.
    /// `a.attribute = new_value`).
    ///
    /// This method should error with `ValueError::CannotMutateImmutableValue` if the value was
    /// frozen or the attribute is immutable (but with `ValueError::OperationNotSupported`
    /// if the operation is not supported on this value, even if the self is immutable,
    /// e.g. for numbers).
    fn set_attr(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError>;

    /// Return a vector of string listing all attribute of the current value, excluding native
    /// methods.
    fn dir_attr(&self) -> Result<Vec<String>, ValueError>;

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
    fn is_in(&self, other: &Value) -> ValueResult;

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
    fn plus(&self) -> ValueResult;

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
    fn minus(&self) -> ValueResult;

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
    fn add(&self, other: Value) -> ValueResult;

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
    fn sub(&self, other: Value) -> ValueResult;

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
    fn mul(&self, other: Value) -> ValueResult;

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
    fn percent(&self, other: Value) -> ValueResult;

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
    fn div(&self, other: Value) -> ValueResult;

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
    fn floor_div(&self, other: Value) -> ValueResult;

    /// Apply the operator pipe to the current value and `other`.
    ///
    /// This is usually the union on set.
    fn pipe(&self, other: Value) -> ValueResult;
}

impl fmt::Debug for TypedValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "Value[{}]({})", self.get_type(), self.to_repr())
    }
}

#[macro_export]
macro_rules! any {
    () => {
        fn as_any(&self) -> &Any {
            self
        }

        fn as_any_mut(&mut self) -> &mut Any {
            self
        }
    }
}

/// A macro to declare method of the trait TypedValue as not supported. This macro take a
/// comma separated list of identifier that can either be the name of a function or set of
/// functions:
///
/// * `iterable`: set of methods for values that are iterable,
/// * `sequence`: set of methods for values that are sequence,
/// * `indexable`: set of methods for values that are indexable,
/// * `set_indexable`: set of methods for values that are setindexable,
/// * `attr`: set of methods to modify value attributes,
/// * `container`: the union of methods in `iterable`, `sequence`, `indexable` and `container`.
/// * `function`: set of methods for function values,
/// * `arithmetic`: set of arithmetic operator (`+`, `-`, `/`, `*`)
/// * `binop`: binary operators: arithmetic, `%`, `|`
#[macro_export]
macro_rules! not_supported {
    (get_hash) => {
        fn get_hash(&self) -> Result<u64, ValueError> {
            Err(ValueError::NotHashableValue)
        }
    };
    (to_int) => {
        fn to_int(&self) -> Result<i64, ValueError> {
            Err(ValueError::OperationNotSupported {
                op: "int()".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (call) => {
        fn call(&self, _call_stack: &[(String, String)], _env: Environment,
                _positional: Vec<Value>, _named: HashMap<String, Value>,
                _args: Option<Value>, _kwargs: Option<Value>) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "call()".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (at) => {
        fn at(&self, index: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "[]".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(index.get_type().to_owned())
            })
        }
    };
    (set_at) => {
        fn set_at(&mut self, index: Value, _new_value: Value) -> Result<(), ValueError> {
            Err(ValueError::OperationNotSupported {
                op: "[] =".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(index.get_type().to_owned())
            })
        }
    };
    (get_attr) => {
        fn get_attr(&self, attribute: &str) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: format!(".{}", attribute), left: self.get_type().to_owned(), right: None })
        }
    };
    (has_attr) => {
        fn has_attr(&self, _attribute: &str) -> Result<bool, ValueError> {
            Err(ValueError::OperationNotSupported {
                op: "has_attr()".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (dir_attr) => {
         fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
             Err(ValueError::OperationNotSupported {
                 op: "dir()".to_owned(), left: self.get_type().to_owned(), right: None })
         }
    };
    (set_attr) => {
        fn set_attr(&mut self, attribute: &str, _new_value: Value) -> Result<(), ValueError> {
            Err(ValueError::OperationNotSupported {
                op: format!(".{} =", attribute), left: self.get_type().to_owned(), right: None })
        }
    };
    (length) => {
        fn length(&self) -> Result<i64, ValueError> {
            Err(ValueError::OperationNotSupported {
                op: "len()".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (plus) => {
        fn plus(&self) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "+".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (minus) => {
        fn minus(&self) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "-".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (slice) => {
        fn slice(&self, _i1: Option<Value>, _i2: Option<Value>, _i3: Option<Value>)
                -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "[::]".to_owned(), left: self.get_type().to_owned(), right: None })
        }
    };
    (iter) => {
        fn iter(&self) -> Result<Box<Iterator<Item=Value>>, ValueError> {
            Err(ValueError::TypeNotX {
                object_type: self.get_type().to_owned(),
                op: "iterable".to_owned()
            })
        }
    };
    (freeze_for_iteration) => {
        fn freeze_for_iteration(&mut self) {}
        fn unfreeze_for_iteration(&mut self) {}
    };
    // Special type: iterable, sequence, indexable, container, function
    (iterable) => { not_supported!(iter, freeze_for_iteration); };
    (sequence) => { not_supported!(length, is_in); };
    (set_indexable) => { not_supported!(set_at); };
    (indexable) => { not_supported!(slice, at, set_indexable); };
    (attr) => { not_supported!(get_attr, has_attr, set_attr, dir_attr); };
    (container) => { not_supported!(iterable, sequence, indexable, attr); };
    (function) => { not_supported!(call); };
    (arithmetic) => { not_supported!(plus, minus, add, sub, mul, div, floor_div); };
    (binop) => { not_supported!(arithmetic, percent, pipe); };
    // Generic
    (is_in) => {
        fn is_in(&self, other: &Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "in".to_owned(),
                left: other.get_type().to_owned(),
                right: Some(self.get_type().to_owned()) })
        }
        // We cannot have descendant if the is_in operation is not defined
        fn is_descendant(&self, _other: &TypedValue) -> bool { false }
    };
    (add) => {
        fn add(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "+".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    (sub) => {
        fn sub(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "-".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    (div) => {
        fn div(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "/".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    (floor_div) => {
        fn floor_div(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "//".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    (mul) => {
        fn mul(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "*".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    (pipe) => {
        fn pipe(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "|".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    (percent) => {
        fn percent(&self, other: Value) -> ValueResult {
            Err(ValueError::OperationNotSupported {
                op: "%".to_owned(),
                left: self.get_type().to_owned(),
                right: Some(other.get_type().to_owned()) })
        }
    };
    // Repetition
    ($a: ident, $($y:ident),+) => {
        not_supported!($a);
        not_supported!($($y),+);
    }
}

/// A default implementation of the compare function, this can be used if the two types of
/// value are differents or numeric. Custom types should implement their own comparison for the
/// last case.
pub fn default_compare(v1: &TypedValue, v2: &TypedValue) -> Result<Ordering, ValueError> {
    Ok(match (v1.get_type(), v2.get_type()) {
        ("bool", "bool") | ("bool", "int") | ("int", "bool") | ("int", "int") => {
            v1.to_int()?.cmp(&(v2.to_int()?))
        }
        ("bool", ..) | ("int", ..) => Ordering::Less,
        (.., "bool") | (.., "int") => Ordering::Greater,
        (x, y) => x.cmp(y),
    })
}

macro_rules! default_compare {
    () => {
        fn compare(&self, other: &TypedValue, _recursion: u32) -> Result<Ordering, ValueError> { default_compare(self, other) }
    }
}

/// Declare the value as immutable.
#[macro_export]
macro_rules! immutable {
    () => {
        fn immutable(&self) -> bool { true }
        fn freeze(&mut self) {}
    }
}

/// A helper enum for defining the level of mutability of an iterable.
///
/// # Examples
///
/// It is made to be used together with default_iterable_mutability! macro, e.g.:
///
/// ```rust,ignore
/// pub struct MyIterable {
///   IterableMutability mutability;
///   // ...
/// }
///
/// impl Value for MyIterable {
///    // define freeze* functions
///    define_iterable_mutability!(mutability)
///    
///    // Later you can use mutability.test()? to
///    // return an error if trying to mutate a frozen object.
/// }
/// ```
#[derive(PartialEq, Eq, Hash, Debug)]
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
    pub fn test(&self) -> Result<(), ValueError> {
        match self {
            IterableMutability::Mutable => Ok(()),
            IterableMutability::Immutable => Err(ValueError::CannotMutateImmutableValue),
            IterableMutability::FrozenForIteration => Err(ValueError::MutationDuringIteration),
        }
    }

    /// Freezes the current value, can be used when implementing the `freeze` function
    /// of the [TypedValue] trait.
    pub fn freeze(&mut self) {
        *self = IterableMutability::Immutable;
    }

    /// Tells wether the current value define a permanently immutable function, to be used
    /// to implement the `immutable` function of the [TypedValue] trait.
    pub fn immutable(&self) -> bool {
        *self == IterableMutability::Immutable
    }

    /// Freezes the current value for iterating over, to be used to implement the
    /// `freeze_for_iteration` function of the [TypedValue] trait.
    pub fn freeze_for_iteration(&mut self) {
        if self.immutable() {
            return;
        }
        *self = IterableMutability::FrozenForIteration
    }

    /// Unfreezes the current value for iterating over, to be used to implement the
    /// `unfreeze_for_iteration` function of the [TypedValue] trait.
    pub fn unfreeze_for_iteration(&mut self) {
        if self.immutable() {
            return;
        }
        *self = IterableMutability::Mutable
    }
}

/// Define functions *freeze_for_iteration/immutable for type using [IterableMutability].
///
/// E.g., if `mutability` is a field of type [IterableMutability], then
/// `define_iterable_mutability(mutability)` would define the four function
/// `immutable`, `freeze_for_iteration` and `unfreeze_for_iteration`
/// for the current trait implementation.
#[macro_export]
macro_rules! define_iterable_mutability {
    ($name: ident) => {
        fn immutable(&self) -> bool { self.$name.immutable() }
        fn freeze_for_iteration(&mut self) { self.$name.freeze_for_iteration() }
        fn unfreeze_for_iteration(&mut self) { self.$name.unfreeze_for_iteration() }
    }
}

impl Value {
    pub fn any_apply<Return>(&self, f: &Fn(&Any) -> Return) -> Return {
        let borrowed = self.0.borrow();
        f(borrowed.as_any())
    }

    pub fn any_apply_mut<Return>(&mut self, f: &Fn(&mut Any) -> Return) -> Return {
        let mut borrowed = self.0.borrow_mut();
        f(borrowed.as_any_mut())
    }

    pub fn immutable(&self) -> bool {
        let borrowed = self.0.borrow();
        borrowed.immutable()
    }
    pub fn freeze(&mut self) {
        let mut borrowed = self.0.borrow_mut();
        borrowed.freeze()
    }
    pub fn freeze_for_iteration(&mut self) {
        let mut borrowed = self.0.borrow_mut();
        borrowed.freeze_for_iteration()
    }
    pub fn unfreeze_for_iteration(&mut self) {
        let mut borrowed = self.0.borrow_mut();
        borrowed.unfreeze_for_iteration()
    }
    pub fn to_str(&self) -> String {
        self.0.borrow().to_str()
    }
    pub fn to_repr(&self) -> String {
        self.0.borrow().to_repr()
    }
    pub fn get_type(&self) -> &'static str {
        let borrowed = self.0.borrow();
        borrowed.get_type()
    }
    pub fn to_bool(&self) -> bool {
        let borrowed = self.0.borrow();
        borrowed.to_bool()
    }
    pub fn to_int(&self) -> Result<i64, ValueError> {
        let borrowed = self.0.borrow();
        borrowed.to_int()
    }
    pub fn get_hash(&self) -> Result<u64, ValueError> {
        let borrowed = self.0.borrow();
        borrowed.get_hash()
    }
    pub fn compare(&self, other: &Value, recursion: u32) -> Result<Ordering, ValueError> {
        self.compare_underlying(other.0.borrow().deref(), recursion)
    }

    pub fn compare_underlying(
        &self,
        other: &TypedValue,
        recursion: u32,
    ) -> Result<Ordering, ValueError> {
        let borrowed = self.0.borrow();
        if recursion > MAX_RECURSION {
            return Err(ValueError::TooManyRecursionLevel);
        }
        if ::std::ptr::eq(borrowed.deref(), other) {
            // Special case for recursive structure, stop if we are pointing to the same object.
            Ok(Ordering::Equal)
        } else {
            borrowed.compare(other, recursion)
        }
    }

    pub fn is_descendant(&self, other: &TypedValue) -> bool {
        if self.same_as(other) {
            return true;
        }
        let try_borrowed = self.0.try_borrow();
        if let Ok(borrowed) = try_borrowed {
            borrowed.is_descendant(other)
        } else {
            // We have already borrowed mutably this value, which means we are trying to mutate it, assigning other to it.
            true
        }
    }

    pub fn call(
        &self,
        call_stack: &[(String, String)],
        env: Environment,
        positional: Vec<Value>,
        named: HashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.call(call_stack, env, positional, named, args, kwargs)
    }
    pub fn at(&self, index: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.at(index)
    }
    pub fn set_at(&mut self, index: Value, new_value: Value) -> Result<(), ValueError> {
        let mut borrowed = self.0.borrow_mut();
        borrowed.set_at(index, new_value)
    }
    pub fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> ValueResult {
        let borrowed = self.0.borrow_mut();
        borrowed.slice(start, stop, stride)
    }
    pub fn iter<'a>(&'a self) -> Result<Box<Iterator<Item = Value> + 'a>, ValueError> {
        let borrowed = self.0.borrow();
        let v: Vec<Value> = borrowed.iter()?.collect();
        Ok(Box::new(v.into_iter()))
    }
    pub fn length(&self) -> Result<i64, ValueError> {
        let borrowed = self.0.borrow();
        borrowed.length()
    }
    pub fn get_attr(&self, attribute: &str) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.get_attr(attribute)
    }
    pub fn has_attr(&self, attribute: &str) -> Result<bool, ValueError> {
        let borrowed = self.0.borrow();
        borrowed.has_attr(attribute)
    }
    pub fn set_attr(&mut self, attribute: &str, new_value: Value) -> Result<(), ValueError> {
        let mut borrowed = self.0.borrow_mut();
        borrowed.set_attr(attribute, new_value)
    }
    pub fn dir_attr(&self) -> Result<Vec<String>, ValueError> {
        let borrowed = self.0.borrow();
        borrowed.dir_attr()
    }
    pub fn is_in(&self, other: &Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.is_in(other)
    }
    pub fn plus(&self) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.plus()
    }
    pub fn minus(&self) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.minus()
    }
    pub fn add(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.add(other)
    }
    pub fn sub(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.sub(other)
    }
    pub fn mul(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.mul(other)
    }
    pub fn percent(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.percent(other)
    }
    pub fn div(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.div(other)
    }
    pub fn floor_div(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.floor_div(other)
    }
    pub fn pipe(&self, other: Value) -> ValueResult {
        let borrowed = self.0.borrow();
        borrowed.pipe(other)
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let borrowed = self.0.borrow();
        write!(f, "{:?}", borrowed)
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.to_str())
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        self.compare(other, 0) == Ok(Ordering::Equal)
    }
}
impl Eq for Value {}

impl Ord for Value {
    fn cmp(&self, other: &Value) -> Ordering {
        self.compare(other, 0).unwrap()
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        if let Ok(r) = self.compare(other, 0) {
            Some(r)
        } else {
            None
        }
    }
}

impl Hash for Value {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        // We panic! if we try to hash a non hashable value, the rest of the code should make sure
        // we do not try to use the Hash trait on non hashble value.
        state.write_u64(self.get_hash().unwrap())
    }
}

/// Define the NoneType type
impl TypedValue for Option<()> {
    immutable!();
    any!();
    fn to_str(&self) -> String {
        "None".to_owned()
    }
    fn to_repr(&self) -> String {
        self.to_str()
    }
    not_supported!(to_int);
    fn get_type(&self) -> &'static str {
        "NoneType"
    }
    fn to_bool(&self) -> bool {
        false
    }
    // just took the result of hash(None) in macos python 2.7.10 interpreter.
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(9_223_380_832_852_120_682)
    }
    default_compare!();
    not_supported!(binop);
    not_supported!(container);
    not_supported!(function);
}

/// Define the int type
impl TypedValue for i64 {
    immutable!();
    any!();
    fn to_str(&self) -> String {
        format!("{}", self)
    }
    fn to_repr(&self) -> String {
        self.to_str()
    }
    fn to_int(&self) -> Result<i64, ValueError> {
        Ok(*self)
    }
    fn get_type(&self) -> &'static str {
        "int"
    }
    fn to_bool(&self) -> bool {
        *self != 0
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(*self as u64)
    }
    default_compare!();
    fn plus(&self) -> ValueResult {
        Ok(Value::new(*self))
    }
    fn minus(&self) -> ValueResult {
        Ok(Value::new(-*self))
    }
    fn add(&self, other: Value) -> ValueResult {
        match other.get_type() {
            "int" | "bool" => Ok(Value::new(self.wrapping_add(other.to_int().unwrap()))),
            _ => other.add(Value::new(*self)),
        }
    }
    fn sub(&self, other: Value) -> ValueResult {
        match other.get_type() {
            "int" | "bool" => Ok(Value::new(self.wrapping_sub(other.to_int().unwrap()))),
            _ => Err(ValueError::OperationNotSupported {
                op: "-".to_owned(),
                left: "int".to_owned(),
                right: Some(other.get_type().to_owned()),
            }),
        }
    }
    fn mul(&self, other: Value) -> ValueResult {
        match other.get_type() {
            "int" | "bool" => Ok(Value::new(self.wrapping_mul(other.to_int().unwrap()))),
            _ => other.mul(Value::new(*self)),
        }
    }
    fn percent(&self, other: Value) -> ValueResult {
        let other = other.to_int()?;
        if other == 0 {
            return Err(ValueError::DivisionByZero);
        }
        let me = self.to_int()?;
        let r = me % other;
        if r == 0 {
            Ok(Value::new(0))
        } else {
            Ok(Value::new(if other.signum() != r.signum() {
                r + other
            } else {
                r
            }))
        }
    }
    fn div(&self, other: Value) -> ValueResult {
        self.floor_div(other)
    }
    fn floor_div(&self, other: Value) -> ValueResult {
        let other = other.to_int()?;
        if other == 0 {
            return Err(ValueError::DivisionByZero);
        }
        let me = self.to_int()?;
        let sig = other.signum() * me.signum();
        let offset = if sig < 0 && me % other != 0 { 1 } else { 0 };
        Ok(Value::new(me / other - offset))
    }
    not_supported!(container);
    not_supported!(function);
    not_supported!(pipe);
}

/// Define the bool type
impl TypedValue for bool {
    immutable!();
    any!();
    fn to_str(&self) -> String {
        if *self {
            "True".to_owned()
        } else {
            "False".to_owned()
        }
    }
    fn to_repr(&self) -> String {
        self.to_str()
    }
    fn to_int(&self) -> Result<i64, ValueError> {
        Ok(if *self { 1 } else { 0 })
    }
    fn get_type(&self) -> &'static str {
        "bool"
    }
    fn to_bool(&self) -> bool {
        *self
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(self.to_int().unwrap() as u64)
    }
    default_compare!();
    fn plus(&self) -> ValueResult {
        Ok(Value::new(self.to_int().unwrap()))
    }
    fn minus(&self) -> ValueResult {
        Ok(Value::new(-self.to_int().unwrap()))
    }
    fn add(&self, other: Value) -> ValueResult {
        match other.get_type() {
            "int" | "bool" => Ok(Value::new(
                self.to_int().unwrap().wrapping_add(other.to_int().unwrap()),
            )),
            _ => other.add(Value::new(*self)),
        }
    }
    fn sub(&self, other: Value) -> ValueResult {
        match other.get_type() {
            "int" | "bool" => Ok(Value::new(
                self.to_int().unwrap().wrapping_sub(other.to_int().unwrap()),
            )),
            _ => Err(ValueError::OperationNotSupported {
                op: "-".to_owned(),
                left: "int".to_owned(),
                right: Some(other.get_type().to_owned()),
            }),
        }
    }
    fn mul(&self, other: Value) -> ValueResult {
        match other.get_type() {
            "int" | "bool" => Ok(Value::new(
                self.to_int().unwrap().wrapping_mul(other.to_int().unwrap()),
            )),
            _ => other.mul(Value::new(*self)),
        }
    }
    fn percent(&self, other: Value) -> ValueResult {
        let other = other.to_int()?;
        if other == 0 {
            return Err(ValueError::DivisionByZero);
        }
        let me = self.to_int()?;
        let r = me % other;
        if r == 0 {
            Ok(Value::new(0))
        } else {
            Ok(Value::new(if other.signum() != r.signum() {
                r + other
            } else {
                r
            }))
        }
    }
    fn div(&self, other: Value) -> ValueResult {
        self.floor_div(other)
    }
    fn floor_div(&self, other: Value) -> ValueResult {
        let other = other.to_int()?;
        if other == 0 {
            return Err(ValueError::DivisionByZero);
        }
        let me = self.to_int()?;
        let sig = other.signum() * me.signum();
        let offset = if sig < 0 && me % other != 0 { 1 } else { 0 };
        Ok(Value::new(me / other - offset))
    }
    not_supported!(container);
    not_supported!(function);
    not_supported!(pipe);
}

impl TypedValue {
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
                let i = if x < 0 { len + x } else { x };
                if i < 0 || i >= len {
                    Err(ValueError::IndexOutOfBound(i))
                } else {
                    Ok(i)
                }
            }
            Err(..) => Err(ValueError::IncorrectParameterType),
        }
    }

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
    /// TypedValue::convert_slice_indices(7, six, None, None).unwrap() == (6, 7, 1)
    /// # );
    /// # assert!(
    /// TypedValue::convert_slice_indices(7, minusone.clone(), None, minusone.clone()).unwrap()
    ///        == (6, -1, -1)
    /// # );
    /// # assert!(
    /// TypedValue::convert_slice_indices(7, minusone, ten, None).unwrap() == (6, 7, 1)
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
                    TypedValue::convert_index_aux(len, start, def_start, clamp, len + clamp);
                let stop = TypedValue::convert_index_aux(len, stop, def_end, clamp, len + clamp);
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
    /// A convenient wrapper around any_apply to actually operate on the underlying type
    pub fn downcast_apply<T: Any, F, Return>(&self, f: F) -> Return
    where
        F: Fn(&T) -> Return,
    {
        self.any_apply(&move |x| f(x.downcast_ref().unwrap()))
    }

    /// A convenient wrapper around any_apply_mut to actually operate on the underlying type
    pub fn downcast_apply_mut<T: Any, F, Return>(&mut self, f: F) -> Return
    where
        F: Fn(&mut T) -> Return,
    {
        self.any_apply_mut(&move |x| f(x.downcast_mut().unwrap()))
    }

    pub fn convert_index(&self, len: i64) -> Result<i64, ValueError> {
        let borrowed = self.0.borrow();
        borrowed.convert_index(len)
    }

    pub fn convert_slice_indices(
        len: i64,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<(i64, i64, i64), ValueError> {
        TypedValue::convert_slice_indices(len, start, stop, stride)
    }
}

// Submodules
pub mod dict;
pub mod function;
pub mod list;
pub mod string;
pub mod tuple;

// Converters
use self::list::List;
use self::tuple::Tuple;
macro_rules! from_X {
    ($x: ty) => {
        impl From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new(a)
            }
        }
    };
    ($x: ty, $y: tt) => {
        impl<T: Into<Value> + Clone> From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new($y::from(a))
            }
        }
    };
    ($x: ty, $y: tt, noT) => {
        impl From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new(a as $y)
            }
        }
    };
    ($y: tt, $($x: tt),+) => {
        impl<$($x: Into<Value> + Clone),+> From<($($x),+)> for Value {
            fn from(a: ($($x),+)) -> Value {
                Value::new($y::from(a))
            }
        }

    };
}

from_X!(i8, i64, noT);
from_X!(i16, i64, noT);
from_X!(i32, i64, noT);
from_X!(u8, i64, noT);
from_X!(u16, i64, noT);
from_X!(u32, i64, noT);
from_X!(u64, i64, noT);
from_X!(i64);
from_X!(bool);
from_X!(String);
impl From<Option<()>> for Value {
    fn from(_a: Option<()>) -> Value {
        Value::new(None)
    }
}
impl From<()> for Value {
    fn from(_a: ()) -> Value {
        Value::new(Tuple::from(()))
    }
}
from_X!((T,), Tuple);
from_X!(Tuple, T1, T2);
from_X!(Tuple, T1, T2, T3);
from_X!(Tuple, T1, T2, T3, T4);
from_X!(Tuple, T1, T2, T3, T4, T5);
from_X!(Tuple, T1, T2, T3, T4, T5, T6);
from_X!(Tuple, T1, T2, T3, T4, T5, T6, T7);
from_X!(Tuple, T1, T2, T3, T4, T5, T6, T7, T8);
from_X!(Tuple, T1, T2, T3, T4, T5, T6, T7, T8, T9);
from_X!(Tuple, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10);
impl<T1: Into<Value> + Eq + Hash + Clone, T2: Into<Value> + Eq + Hash + Clone> From<HashMap<T1, T2>>
    for Value
{
    fn from(a: HashMap<T1, T2>) -> Value {
        Value::new(dict::Dictionary::from(a))
    }
}
impl<T1: Into<Value> + Eq + Hash + Clone, T2: Into<Value> + Eq + Hash + Clone>
    From<LinkedHashMap<T1, T2>> for Value
{
    fn from(a: LinkedHashMap<T1, T2>) -> Value {
        Value::new(dict::Dictionary::from(a))
    }
}
from_X!(Vec<T>, List);
impl<'a> From<&'a str> for Value {
    fn from(a: &'a str) -> Value {
        Value::new(a.to_owned())
    }
}

// A convenient macro for testing and documentation.
#[macro_export]
#[doc(hidden)]
macro_rules! int_op {
    ($v1:tt. $op:ident($v2:expr)) => {
        $v1.$op(Value::new($v2)).unwrap().to_int().unwrap()
    };
    ($v1:tt. $op:ident()) => {
        $v1.$op().unwrap().to_int().unwrap()
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_index() {
        assert_eq!(Ok(6), Value::new(6).convert_index(7));
        assert_eq!(Ok(6), Value::new(-1).convert_index(7));
        assert_eq!(
            Ok((6, 7, 1)),
            TypedValue::convert_slice_indices(7, Some(Value::new(6)), None, None)
        );
        assert_eq!(
            Ok((6, -1, -1)),
            TypedValue::convert_slice_indices(7, Some(Value::new(-1)), None, Some(Value::new(-1)))
        );
        assert_eq!(
            Ok((6, 7, 1)),
            TypedValue::convert_slice_indices(7, Some(Value::new(-1)), Some(Value::new(10)), None)
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
    fn test_arithmetic_operators() {
        assert_eq!(1, int_op!(1.plus())); // 1.plus() = +1 = 1
        assert_eq!(-1, int_op!(1.minus())); // 1.minus() = -1
        assert_eq!(3, int_op!(1.add(2))); // 1.add(2) = 1 + 2 = 3
        assert_eq!(-1, int_op!(1.sub(2))); // 1.sub(2) = 1 - 2 = -1
        assert_eq!(6, int_op!(2.mul(3))); // 2.mul(3) = 2 * 3 = 6
                                          // Remainder of the floored division: 5.percent(3) = 5 % 3 = 2
        assert_eq!(2, int_op!(5.percent(3)));
        assert_eq!(3, int_op!(7.div(2))); // 7.div(2) = 7 / 2 = 3
    }

    #[test]
    fn can_implement_compare() {
        #[derive(Debug, PartialEq, Eq, Ord, PartialOrd)]
        struct WrappedNumber(u64);

        /// Define the NoneType type
        impl TypedValue for WrappedNumber {
            immutable!();
            any!();
            fn to_str(&self) -> String {
                format!("{:?}", self)
            }
            fn to_repr(&self) -> String {
                self.to_str()
            }
            not_supported!(to_int);
            fn get_type(&self) -> &'static str {
                "WrappedNumber"
            }
            fn to_bool(&self) -> bool {
                false
            }
            fn get_hash(&self) -> Result<u64, ValueError> {
                Ok(self.0)
            }
            fn compare<'a>(
                &'a self,
                other: &TypedValue,
                _recursion: u32,
            ) -> Result<std::cmp::Ordering, ValueError> {
                match other.get_type() {
                    "WrappedNumber" => {
                        let other = other.as_any().downcast_ref::<Self>().unwrap();
                        Ok(std::cmp::Ord::cmp(self, other))
                    }
                    _ => default_compare(self, other),
                }
            }
            not_supported!(binop);
            not_supported!(container);
            not_supported!(function);
        }

        let one = Value::new(WrappedNumber(1));
        let another_one = Value::new(WrappedNumber(1));
        let two = Value::new(WrappedNumber(2));
        let not_wrapped_number: Value = 1.into();

        use std::cmp::Ordering::*;

        assert_eq!(one.compare(&one, 0), Ok(Equal));
        assert_eq!(one.compare(&another_one, 0), Ok(Equal));
        assert_eq!(one.compare(&two, 0), Ok(Less));
        assert_eq!(two.compare(&one, 0), Ok(Greater));
        assert_eq!(one.compare(&not_wrapped_number, 0), Ok(Greater));
        assert_eq!(not_wrapped_number.compare(&one, 0), Ok(Less));
    }
}
