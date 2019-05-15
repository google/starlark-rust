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

//! String interpolation-related code.

use crate::syntax::errors::SyntaxError;
use crate::values::error::*;
use codemap::Span;
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};

/// Operator `%` format or evaluation errors
#[derive(Clone, Debug)]
pub enum StringInterpolationError {
    /// Format of the interpolation string is incorrect.
    Format,
    /// Trying to interpolate with %c an integer that is not in the UTF-8 range.
    ValueNotInUTFRange(u32),
    /// Interpolation parameter is too big for the format string.
    TooManyParameters,
    /// Interpolation parameter is too small for the format string.
    NotEnoughParameters,
    /// Value for `%s` is required to be a char
    ValueNotChar,
}

impl SyntaxError for StringInterpolationError {
    fn to_diagnostic(self, file_span: Span) -> Diagnostic {
        let (label, message, code) = match self {
            StringInterpolationError::Format => (
                "Interpolation string format incorrect".to_owned(),
                concat!(
                    "Interpolation string format is incorrect:",
                    " '%' must be followed by an optional name and a specifier ",
                    "('s', 'r', 'd', 'i', 'o', 'x', 'X', 'c')"
                )
                .to_owned(),
                INTERPOLATION_FORMAT_ERROR_CODE,
            ),
            StringInterpolationError::ValueNotInUTFRange(ref c) => (
                format!("Invalid codepoint 0x{:x}", c),
                format!(
                    concat!(
                        "Value 0x{:x} passed for %c formattter is not a valid",
                        " UTF-8 codepoint"
                    ),
                    c
                ),
                INTERPOLATION_OUT_OF_UTF8_RANGE_ERROR_CODE,
            ),
            StringInterpolationError::TooManyParameters => (
                "Too many arguments for format string".to_owned(),
                "Too many arguments for format string".to_owned(),
                INTERPOLATION_TOO_MANY_PARAMS_ERROR_CODE,
            ),
            StringInterpolationError::NotEnoughParameters => (
                "Not enough arguments for format string".to_owned(),
                "Not enough arguments for format string".to_owned(),
                INTERPOLATION_NOT_ENOUGH_PARAMS_ERROR_CODE,
            ),
            StringInterpolationError::ValueNotChar => (
                "'%c' formatter requires a single-character string".to_owned(),
                "'%c' formatter requires a single-character string".to_owned(),
                INTERPOLATION_VALUE_IS_NOT_CHAR_ERROR_CODE,
            ),
        };
        let sl = SpanLabel {
            span: file_span,
            style: SpanStyle::Primary,
            label: Some(label),
        };
        Diagnostic {
            level: Level::Error,
            message,
            code: Some(code.to_owned()),
            spans: vec![sl],
        }
    }
}
