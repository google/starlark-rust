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
use crate::values::Value;
use codemap::Span;
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use std::convert::TryFrom;
use std::iter;

/// Operator `%` format or evaluation errors
#[derive(Clone, Debug)]
pub enum StringInterpolationError {
    /// `)` is not found when parsing `%(name)` expression.
    UnexpectedEOFClosingParen,
    /// `%` must be followed by specifier.
    UnexpectedEOFPercent,
    /// `%z` where `z` is unknown specifier.
    UnknownSpecifier(char),
    /// Trying to interpolate with %c an integer that is not in the UTF-8 range.
    ValueNotInUTFRange(i64),
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
            StringInterpolationError::UnexpectedEOFClosingParen => (
                "Unexpected EOF in format string when looking for closing paren".to_owned(),
                "Could not found ')' when parsing '%(name)f' expression".to_owned(),
                INTERPOLATION_UNEXPECTED_EOF_CLOSING_PAREN,
            ),
            StringInterpolationError::UnexpectedEOFPercent => (
                "End of string while expecting format specifier".to_owned(),
                concat!(
                    "Interpolation string format is incorrect:",
                    " '%' must be followed by an optional name and a specifier ",
                    "('s', 'r', 'd', 'i', 'o', 'x', 'X', 'c') or '%'",
                )
                .to_owned(),
                INTERPOLATION_UNEXPECTED_EOF_PERCENT,
            ),
            StringInterpolationError::UnknownSpecifier(c) => (
                format!("Unknown format string specifier '{}'", c.escape_default()),
                concat!(
                    "Interpolation string format is incorrect:",
                    " '%' must be followed by an optional name and a specifier ",
                    "('s', 'r', 'd', 'i', 'o', 'x', 'X', 'c') or '%'",
                )
                .to_owned(),
                INTERPOLATION_UNKNOWN_SPECIFIER,
            ),
            StringInterpolationError::ValueNotInUTFRange(ref c) => (
                format!("Invalid codepoint 0x{:x}", c),
                format!(
                    concat!(
                        "Value 0x{:x} passed for %c formatter is not a valid",
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

/// Format char
pub(crate) enum ArgFormat {
    // str(x)
    Str,
    // repr(x)
    Repr,
    // signed integer decimal
    Dec,
    // signed octal
    Oct,
    // signed hexadecimal, lowercase
    HexLower,
    // signed hexadecimal, uppercase
    HexUpper,
    // x for string, chr(x) for int
    Char,
    // `%` sign
    Percent,
}

impl ArgFormat {
    fn format_arg(&self, out: &mut String, arg: Value) -> Result<(), ValueError> {
        use std::fmt::Write;

        match self {
            ArgFormat::Str => write!(out, "{}", arg.to_str()).unwrap(),
            ArgFormat::Repr => write!(out, "{}", arg.to_repr()).unwrap(),
            ArgFormat::Dec => write!(out, "{}", arg.to_int()?).unwrap(),
            ArgFormat::Oct => {
                let v = arg.to_int()?;
                write!(
                    out,
                    "{}{:o}",
                    if v < 0 { "-" } else { "" },
                    v.wrapping_abs() as u64
                )
                .unwrap();
            }
            ArgFormat::HexLower => {
                let v = arg.to_int()?;
                write!(
                    out,
                    "{}{:x}",
                    if v < 0 { "-" } else { "" },
                    v.wrapping_abs() as u64
                )
                .unwrap();
            }
            ArgFormat::HexUpper => {
                let v = arg.to_int()?;
                write!(
                    out,
                    "{}{:X}",
                    if v < 0 { "-" } else { "" },
                    v.wrapping_abs() as u64
                )
                .unwrap();
            }
            ArgFormat::Char => match arg.get_type() {
                "string" => {
                    if arg.length()? != 1 {
                        return Err(StringInterpolationError::ValueNotChar.into());
                    } else {
                        write!(out, "{}", arg.to_str()).unwrap();
                    }
                }
                _ => {
                    let i = arg.to_int()?;
                    let codepoint = match u32::try_from(i) {
                        Ok(codepoint) => codepoint,
                        Err(_) => {
                            return Err(StringInterpolationError::ValueNotInUTFRange(i).into())
                        }
                    };
                    match std::char::from_u32(codepoint) {
                        Some(c) => write!(out, "{}", c).unwrap(),
                        None => {
                            return Err(StringInterpolationError::ValueNotInUTFRange(i64::from(
                                codepoint,
                            ))
                            .into())
                        }
                    }
                }
            },
            ArgFormat::Percent => {
                write!(out, "%").unwrap();
            }
        }
        Ok(())
    }
}

// %(name)s or %s
enum NamedOrPositional {
    Named(String),
    Positional,
}

/// Parsed format string
pub(crate) struct ArgsFormat {
    /// String before first parameter
    init: String,
    /// Number of positional arguments
    positional_count: usize,
    /// Number of named arguments
    named_count: usize,
    /// Arguments followed by uninterpreted strings
    parameters: Vec<(NamedOrPositional, ArgFormat, String)>,
}

impl ArgsFormat {
    fn append_literal(&mut self, c: char) {
        if let Some(p) = self.parameters.last_mut() {
            p.2.push(c);
        } else {
            self.init.push(c)
        }
    }

    pub fn parse(format: &str) -> Result<ArgsFormat, ValueError> {
        let mut result = ArgsFormat {
            init: String::new(),
            positional_count: 0,
            named_count: 0,
            parameters: Vec::new(),
        };
        let mut chars = format.chars();
        while let Some(c) = chars.next() {
            if c != '%' {
                result.append_literal(c);
            } else {
                let next = chars
                    .next()
                    .ok_or(StringInterpolationError::UnexpectedEOFPercent)?;
                let (named_or_positional, format_char) = if next == '(' {
                    let mut name = String::new();
                    loop {
                        match chars.next() {
                            None => {
                                return Err(
                                    StringInterpolationError::UnexpectedEOFClosingParen.into()
                                )
                            }
                            Some(')') => {
                                break;
                            }
                            Some(c) => name.push(c),
                        }
                    }
                    (
                        NamedOrPositional::Named(name),
                        chars
                            .next()
                            .ok_or(StringInterpolationError::UnexpectedEOFPercent)?,
                    )
                } else {
                    (NamedOrPositional::Positional, next)
                };
                let format = match format_char {
                    's' => ArgFormat::Str,
                    'r' => ArgFormat::Repr,
                    'd' | 'i' => ArgFormat::Dec,
                    'o' => ArgFormat::Oct,
                    'x' => ArgFormat::HexLower,
                    'X' => ArgFormat::HexUpper,
                    'c' => ArgFormat::Char,
                    '%' => match named_or_positional {
                        NamedOrPositional::Positional => {
                            result.append_literal('%');
                            continue;
                        }
                        NamedOrPositional::Named(_) => {
                            // In both Python and Starlark Go implementations
                            // `%(n)%` consumes named argument, but
                            // `%%` does not consume positional argument.
                            // So `Percent` variant is added only when `ArgFormat` is `Named`.
                            ArgFormat::Percent
                        }
                    },
                    c => return Err(StringInterpolationError::UnknownSpecifier(c).into()),
                };
                match named_or_positional {
                    NamedOrPositional::Positional => {
                        result.positional_count += 1;
                    }
                    NamedOrPositional::Named(..) => {
                        result.named_count += 1;
                    }
                }
                result
                    .parameters
                    .push((named_or_positional, format, String::new()));
            }
        }
        Ok(result)
    }

    pub fn format(self, other: &Value) -> Result<String, ValueError> {
        let mut r = self.init;
        let other_iter;
        let mut arg_iter: Box<dyn Iterator<Item = Value>> = if self.positional_count > 1 {
            other_iter = Some(other.iter()?);
            other_iter.as_ref().unwrap().iter()
        } else if self.positional_count == 1 {
            Box::new(iter::once(other.clone()))
        } else if self.named_count != 0 {
            Box::new(iter::empty())
        } else {
            // If both positional count is zero and named count is zero
            // we should check that iterable has zero elements.
            other_iter = Some(other.iter()?);
            other_iter.as_ref().unwrap().iter()
        };
        for (named_or_positional, format, tail) in self.parameters {
            let arg = match named_or_positional {
                NamedOrPositional::Positional => match arg_iter.next() {
                    Some(a) => a,
                    None => return Err(StringInterpolationError::NotEnoughParameters.into()),
                },
                NamedOrPositional::Named(name) => other.at(Value::new(name))?,
            };
            format.format_arg(&mut r, arg)?;
            r.push_str(&tail);
        }

        if arg_iter.next().is_some() {
            return Err(StringInterpolationError::TooManyParameters.into());
        }

        Ok(r)
    }
}

#[cfg(test)]
mod test {
    use crate::values::Value;
    use std::collections::HashMap;
    use std::convert::TryFrom;

    #[test]
    fn test_string_interpolation() {
        // "Hello %s, your score is %d" % ("Bob", 75) == "Hello Bob, your score is 75"
        assert_eq!(
            Value::from("Hello %s, your score is %d")
                .percent(&Value::from(("Bob", 75)))
                .unwrap(),
            Value::from("Hello Bob, your score is 75")
        );

        // "%d %o %x %c" % (65, 65, 65, 65) == "65 101 41 A"
        assert_eq!(
            Value::from("%d %o %x %c")
                .percent(&Value::from((65, 65, 65, 65)))
                .unwrap(),
            Value::from("65 101 41 A")
        );

        // "%(greeting)s, %(audience)s" % {"greeting": "Hello", "audience": "world"} ==
        //      "Hello, world"
        let mut d = Value::try_from(HashMap::<String, Value>::new()).unwrap();
        d.set_at(Value::from("greeting"), Value::from("Hello"))
            .unwrap();
        d.set_at(Value::from("audience"), Value::from("world"))
            .unwrap();
        assert_eq!(
            Value::from("%(greeting)s, %(audience)s")
                .percent(&d)
                .unwrap(),
            Value::from("Hello, world")
        );

        // Both Python and Starlark Go behave this way:
        // "%s%(a)%" % {"a": 1} == "{\"a\": 1}%"
        // "%s%(a)s" % {"a": 1} == "{\"a\": 1}1"
        let mut d = Value::try_from(HashMap::<String, Value>::new()).unwrap();
        d.set_at(Value::from("a"), Value::from(1)).unwrap();
        assert_eq!(
            Value::from("%s%(a)%").percent(&d).unwrap(),
            Value::from("{\"a\": 1}%")
        );
        assert_eq!(
            Value::from("%s%(a)s").percent(&d).unwrap(),
            Value::from("{\"a\": 1}1")
        );
    }
}
