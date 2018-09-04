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

use super::ast::AstStatement;
use super::errors::SyntaxError;
use super::grammar::{parse_build_file, parse_starlark};
use super::lexer::{Lexer, LexerError, LexerIntoIter, LexerItem, Token};
use codemap::{CodeMap, Span};
use codemap_diagnostic::{Diagnostic, Level, SpanLabel, SpanStyle};
use std::error::Error;
use std::fs::File;
use std::io::prelude::*;
use std::sync::{Arc, Mutex};
extern crate lalrpop_util as lu;

// TODO: move that code in some common error code list?
// CP Prefix = Critical Parsing
const INVALID_TOKEN_ERROR_CODE: &'static str = "CP00";
const UNEXPECTED_TOKEN_ERROR_CODE: &'static str = "CP01";
const EXTRA_TOKEN_ERROR_CODE: &'static str = "CP02";
const RESERVED_KEYWORD_ERROR_CODE: &'static str = "CP03";
const IO_ERROR_CODE: &'static str = "CP04";

fn one_of(expected: &Vec<String>) -> String {
    let mut result = String::new();
    for (i, e) in expected.iter().enumerate() {
        let sep = match i {
            0 => "one of",
            _ if i < expected.len() - 1 => ",",
            // Last expected message to be written
            _ => " or",
        };
        result.push_str(&format!("{} {}", sep, e));
    }
    result
}

impl SyntaxError for lu::ParseError<u64, Token, LexerError> {
    /// Convert the error to a codemap diagnostic.
    ///
    /// To build this diagnostic, the method needs the file span corresponding to the parsed
    /// file.
    fn to_diagnostic(self, file_span: Span) -> Diagnostic {
        let (label, message) = match self {
            lu::ParseError::InvalidToken { .. } => (
                Some("Invalid token".to_owned()),
                "Parse error: invalid token".to_owned(),
            ),
            lu::ParseError::UnrecognizedToken {
                token: Some((_x, Token::Reserved(ref s), _y)),
                expected: ref _unused,
            } => (
                Some("Reserved keyword".to_owned()),
                format!("Parse error: cannot use reserved keyword {}", s),
            ),
            lu::ParseError::ExtraToken {
                token: (_x, Token::Reserved(ref s), _y),
            } => (
                Some("Reserved keyword".to_owned()),
                format!("Parse error: cannot use reserved keyword {}", s),
            ),
            lu::ParseError::UnrecognizedToken {
                token: Some((_x, ref t, ..)),
                ref expected,
            } => (
                Some(format!("Expected {}", one_of(expected))),
                format!(
                    "Parse error: unexpected {} here, expected {}",
                    t,
                    one_of(expected)
                ),
            ),
            lu::ParseError::ExtraToken {
                token: (_x, ref t, ..),
            } => (
                Some(format!("Extraneous {}", t)),
                format!("Parse error: extraneous token {}", t),
            ),
            lu::ParseError::UnrecognizedToken { .. } => {
                (None, "Parse error: unexpected end of file".to_owned())
            }
            lu::ParseError::User { ref error } => return error.to_diagnostic(file_span),
        };
        let sl = SpanLabel {
            span: match self {
                lu::ParseError::InvalidToken { ref location } => {
                    file_span.subspan(*location, *location)
                }
                lu::ParseError::UnrecognizedToken {
                    token: Some((x, .., y)),
                    ..
                } => file_span.subspan(x, y),
                lu::ParseError::UnrecognizedToken { .. } => {
                    let x = file_span.high() - file_span.low();
                    file_span.subspan(x, x)
                }
                lu::ParseError::ExtraToken { token: (x, .., y) } => file_span.subspan(x, y),
                lu::ParseError::User { .. } => unreachable!(),
            },
            style: SpanStyle::Primary,
            label,
        };

        Diagnostic {
            level: Level::Error,
            message,
            code: Some(
                match self {
                    lu::ParseError::InvalidToken { .. } => INVALID_TOKEN_ERROR_CODE,
                    lu::ParseError::UnrecognizedToken {
                        token: Some((_x, Token::Reserved(..), ..)),
                        ..
                    }
                    | lu::ParseError::ExtraToken {
                        token: (_x, Token::Reserved(..), ..),
                    } => RESERVED_KEYWORD_ERROR_CODE,
                    lu::ParseError::UnrecognizedToken { .. } => UNEXPECTED_TOKEN_ERROR_CODE,
                    lu::ParseError::ExtraToken { .. } => EXTRA_TOKEN_ERROR_CODE,
                    lu::ParseError::User { .. } => unreachable!(),
                }.to_owned(),
            ),
            spans: vec![sl],
        }
    }
}

macro_rules! iotry {
    ($e:expr) => {
        match $e {
            Ok(val) => val,
            Err(err) => {
                return Err(Diagnostic {
                    level: Level::Error,
                    message: format!("IOError: {}", err.description()),
                    code: Some(IO_ERROR_CODE.to_owned()),
                    spans: vec![],
                })
            }
        }
    };
}

/// Parse a build file (if build is true) or a starlark file provided as a content using a custom
/// lexer.
///
/// # arguments
///
/// * codemap: the codemap object used for diagnostics
/// * filename: the name of the file being parsed, for diagnostics
/// * content: the content to parse
/// * build: set to true if you want to parse a BUILD file or false to parse a .bzl file.
/// * lexer: the lexer to use for parsing
#[doc(hidden)]
pub fn parse_lexer<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>>(
    map: &Arc<Mutex<CodeMap>>,
    filename: &str,
    content: &str,
    build: bool,
    lexer: T2,
) -> Result<AstStatement, Diagnostic> {
    let filespan = {
        map.lock()
            .unwrap()
            .add_file(filename.to_string(), content.to_string())
            .span
    };
    match {
        if build {
            parse_build_file(content, filespan, lexer)
        } else {
            parse_starlark(content, filespan, lexer)
        }
    } {
        Result::Ok(v) => Result::Ok(v),
        Result::Err(p) => Result::Err(p.to_diagnostic(filespan)),
    }
}

/// Parse a build file (if build is true) or a starlark file provided as a content.
///
/// # arguments
///
/// * codemap: the codemap object used for diagnostics
/// * filename: the name of the file being parsed, for diagnostics
/// * content: the content to parse
/// * build: set to true if you want to parse a BUILD file or false to parse a .bzl file.
#[doc(hidden)]
pub fn parse(
    map: &Arc<Mutex<CodeMap>>,
    filename: &str,
    content: &str,
    build: bool,
) -> Result<AstStatement, Diagnostic> {
    let content2 = content.to_owned();
    parse_lexer(map, filename, content, build, Lexer::new(&content2))
}

/// Parse a build file (if build is true) or a starlark file, reading the content from the file
/// system.
///
/// # arguments
///
/// * codemap: the codemap object used for diagnostics
/// * path: the path to the file to parse
/// * build: set to true if you want to parse a BUILD file or false to parse a .bzl file.
///
/// # Note
///
/// This method unwrap the path to a unicode string, which can panic.
#[doc(hidden)]
pub fn parse_file(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    build: bool,
) -> Result<AstStatement, Diagnostic> {
    let mut content = String::new();
    let mut file = iotry!(File::open(path));
    iotry!(file.read_to_string(&mut content));
    parse(map, path, &content, build)
}
