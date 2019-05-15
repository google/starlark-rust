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

//! Module define the common engine error.

use crate::syntax::errors::SyntaxError;
use crate::values::string::interpolation::StringInterpolationError;
use crate::values::*;
use codemap::Span;
use codemap_diagnostic::{Diagnostic, SpanLabel, SpanStyle};

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
pub const INTEGER_OVERFLOW_ERROR_CODE: &str = "CV16";

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
    TypeNotX { object_type: String, op: String },
    /// Division by 0
    DivisionByZero,
    /// Arithmetic operation results in integer overflow.
    IntegerOverflow,
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
    /// String interpolation errors
    StringInterpolation(StringInterpolationError),
    /// Too many recursion in internal operation
    TooManyRecursionLevel,
    /// Recursive data structure are not allowed because they would allow infinite loop.
    UnsupportedRecursiveDataStructure,
    /// It is not allowed to mutate a structure during iteration.
    MutationDuringIteration,
    /// A type was used which isn't supported with the current feature set. Wraps the type name.
    TypeNotSupported(String),
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

impl Into<ValueError> for StringInterpolationError {
    fn into(self) -> ValueError {
        ValueError::StringInterpolation(self)
    }
}

impl SyntaxError for ValueError {
    fn to_diagnostic(self, file_span: Span) -> Diagnostic {
        match self {
            ValueError::DiagnosedError(d) => d,
            ValueError::StringInterpolation(e) => e.to_diagnostic(file_span),
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
                        ValueError::IntegerOverflow => "Integer overflow".to_owned(),
                        ValueError::CannotMutateImmutableValue => "Immutable".to_owned(),
                        ValueError::IncorrectParameterType => {
                            "Type of parameters mismatch".to_owned()
                        }
                        ValueError::IndexOutOfBound(..) => "Index out of bound".to_owned(),
                        ValueError::NotHashableValue => "Value is not hashable".to_owned(),
                        ValueError::KeyNotFound(..) => "Key not found".to_owned(),
                        ValueError::TooManyRecursionLevel => "Too many recursion".to_owned(),
                        ValueError::UnsupportedRecursiveDataStructure => {
                            "Unsupported recursive data structure".to_owned()
                        }
                        ValueError::MutationDuringIteration => {
                            "Cannot mutate an iterable while iterating".to_owned()
                        }
                        ValueError::TypeNotSupported(ref t) => {
                            format!("Attempt to construct unsupported type ({})", t)
                        }
                        // handled above
                        ValueError::DiagnosedError(..) | ValueError::StringInterpolation(..) => {
                            unreachable!()
                        }
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
                        ValueError::IntegerOverflow => "Integer overflow".to_owned(),
                        ValueError::CannotMutateImmutableValue => "Immutable".to_owned(),
                        ValueError::IncorrectParameterType => {
                            "Type of parameters mismatch".to_owned()
                        }
                        ValueError::IndexOutOfBound(ref b) => {
                            format!("Index {} is out of bound", b)
                        }
                        ValueError::NotHashableValue => "Value is not hashable".to_owned(),
                        ValueError::KeyNotFound(ref k) => format!("Key '{}' was not found", k),
                        ValueError::TooManyRecursionLevel => "Too many recursion levels".to_owned(),
                        ValueError::UnsupportedRecursiveDataStructure => concat!(
                            "This operation create a recursive data structure. Recursive data",
                            "structure are disallowed because infinite loops are disallowed in Starlark."
                        ).to_owned(),
                        ValueError::MutationDuringIteration => {
                            "This operation mutate an iterable for an iterator is borrowed.".to_owned()
                        }
                        ValueError::TypeNotSupported(ref t) => {
                            format!("Type `{}` is not supported. Perhaps you need to enable some crate feature?", t)
                        }
                        // handled above
                        ValueError::DiagnosedError(..) | ValueError::StringInterpolation(..) => unreachable!(),
                    },
                    code: Some(
                        match self {
                            ValueError::OperationNotSupported { .. } | ValueError::TypeNotSupported(..) => NOT_SUPPORTED_ERROR_CODE,
                            ValueError::TypeNotX { .. } => NOT_SUPPORTED_ERROR_CODE,
                            ValueError::DivisionByZero => DIVISION_BY_ZERO_ERROR_CODE,
                            ValueError::IntegerOverflow => INTEGER_OVERFLOW_ERROR_CODE,
                            ValueError::CannotMutateImmutableValue => IMMUTABLE_ERROR_CODE,
                            ValueError::IncorrectParameterType => {
                                INCORRECT_PARAMETER_TYPE_ERROR_CODE
                            }
                            ValueError::IndexOutOfBound(..) => OUT_OF_BOUND_ERROR_CODE,
                            ValueError::NotHashableValue => NOT_HASHABLE_VALUE_ERROR_CODE,
                            ValueError::KeyNotFound(..) => KEY_NOT_FOUND_ERROR_CODE,
                            ValueError::Runtime(e) => e.code,
                            ValueError::TooManyRecursionLevel => {
                                TOO_MANY_RECURSION_LEVEL_ERROR_CODE
                            }
                            ValueError::UnsupportedRecursiveDataStructure => {
                                UNSUPPORTED_RECURSIVE_DATA_STRUCTURE_ERROR_CODE
                            }
                            ValueError::MutationDuringIteration => {
                                CANNOT_MUTATE_DURING_ITERATION_ERROR_CODE
                            }
                            // handled above
                            ValueError::DiagnosedError(..) | ValueError::StringInterpolation(..) => unreachable!(),
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
