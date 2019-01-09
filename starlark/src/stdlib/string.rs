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

//! Methods for the `string` type.

use std::str::FromStr;
use values::*;

// Errors -- UF = User Failure -- Failure that should be expected by the user (e.g. from a fail()).
pub const SUBSTRING_INDEX_FAILED_ERROR_CODE: &str = "UF00";
pub const FORMAT_STRING_UNMATCHED_BRACKET_ERROR_CODE: &str = "UF01";
pub const FORMAT_STRING_ORDER_INDEX_MIX_ERROR_CODE: &str = "UF02";
pub const FORMAT_STRING_INVALID_SPECIFIER_ERROR_CODE: &str = "UF03";
pub const FORMAT_STRING_INVALID_CHARACTER_ERROR_CODE: &str = "UF04";

macro_rules! ok {
    ($e:expr) => {
        return Ok(Value::from($e));
    };
}

macro_rules! check_string {
    ($e:ident, $fn:ident) => {
        check_type!($e, concat!("string.", stringify!($fn)), string)
    };
}

fn format_capture<T: Iterator<Item = Value>>(
    capture: &str,
    it: &mut T,
    captured_by_index: &mut bool,
    captured_by_order: &mut bool,
    args: &Value,
    kwargs: &Value,
) -> Result<String, ValueError> {
    let (n, conv) = {
        if let Some(x) = capture.find('!') {
            (capture.get(1..x).unwrap(), capture.get(x + 1..).unwrap())
        } else {
            (capture.get(1..).unwrap(), "s")
        }
    };
    let conv_s = |x: Value| x.to_str();
    let conv_r = |x: Value| x.to_repr();
    let conv: &Fn(Value) -> String = match conv {
        "s" => &conv_s,
        "r" => &conv_r,
        c => starlark_err!(
            FORMAT_STRING_INVALID_SPECIFIER_ERROR_CODE,
            format!(
                concat!(
                    "'{}' is not a valid format string specifier, only ",
                    "'s' and 'r' are valid specifiers",
                ),
                c
            ),
            "Invalid format string specifier".to_owned()
        ),
    };
    if n.is_empty() {
        if *captured_by_index {
            starlark_err!(
                FORMAT_STRING_ORDER_INDEX_MIX_ERROR_CODE,
                concat!(
                    "Cannot mix manual field specification and ",
                    "automatic field numbering in format string"
                )
                .to_owned(),
                "Mixed manual and automatic field numbering".to_owned()
            )
        } else {
            *captured_by_order = true;
            if let Some(x) = it.next() {
                return Ok(conv(x));
            } else {
                starlark_err!(
                    OUT_OF_BOUND_ERROR_CODE,
                    "Not enough parameters in format string".to_owned(),
                    "Not enough parameters".to_owned()
                )
            }
        }
    } else if n.chars().all(|c| c.is_ascii_digit()) {
        if *captured_by_order {
            starlark_err!(
                FORMAT_STRING_ORDER_INDEX_MIX_ERROR_CODE,
                concat!(
                    "Cannot mix manual field specification and ",
                    "automatic field numbering in format string"
                )
                .to_owned(),
                "Mixed manual and automatic field numbering".to_owned()
            )
        } else {
            *captured_by_index = true;
            Ok(conv(args.at(Value::from(i64::from_str(n).unwrap()))?))
        }
    } else {
        if let Some(x) = n.chars().find(|c| match c {
            '.' | ',' | '[' | ']' => true,
            _ => false,
        }) {
            starlark_err!(
                FORMAT_STRING_INVALID_CHARACTER_ERROR_CODE,
                format!("Invalid character '{}' inside replacement field", x),
                format!("Invalid character '{}'", x)
            )
        }
        Ok(conv(kwargs.at(Value::from(n))?))
    }
}

// This does not exists in rust, split would cut the string incorrectly and split_whitespace
// cannot take a n parameter.
fn splitn_whitespace(s: &str, maxsplit: usize) -> Vec<String> {
    let mut v = Vec::new();
    let mut cur = String::new();
    let mut split = 1;
    let mut eat_ws = true;
    for c in s.chars() {
        if split >= maxsplit && !eat_ws {
            cur.push(c)
        } else if c.is_whitespace() {
            if !cur.is_empty() {
                v.push(cur);
                cur = String::new();
                split += 1;
                eat_ws = true;
            }
        } else {
            eat_ws = false;
            cur.push(c)
        }
    }
    if !cur.is_empty() {
        v.push(cur)
    }
    v
}

fn rsplitn_whitespace(s: &str, maxsplit: usize) -> Vec<String> {
    let mut v = Vec::new();
    let mut cur = String::new();
    let mut split = 1;
    let mut eat_ws = true;
    for c in s.chars().rev() {
        if split >= maxsplit && !eat_ws {
            cur.push(c)
        } else if c.is_whitespace() {
            if !cur.is_empty() {
                v.push(cur.chars().rev().collect());
                cur = String::new();
                split += 1;
                eat_ws = true;
            }
        } else {
            eat_ws = false;
            cur.push(c)
        }
    }
    if !cur.is_empty() {
        v.push(cur.chars().rev().collect());
    }
    v.reverse();
    v
}

starlark_module! {global =>
    /// [string.elems](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·elems
    /// ): returns an iterable of the bytes values of a string.
    ///
    /// `S.elems()` returns an iterable value containing the
    /// sequence of numeric bytes values in the string S.
    ///
    /// To materialize the entire sequence of bytes, apply `list(...)` to the result.
    ///
    /// Example:
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// list("Hello, 世界".elems()) == [
    ///     72, 101, 108, 108, 111, 44, 32, 228, 184, 150, 231, 149, 140]
    /// # )"#).unwrap());
    /// ```
    string.elems(this) {
        // Note that we return a list here... Which is not equivalent to the go implementation.
        ok!(this.to_str().into_bytes())
    }

    /// [string.capitalize](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·capitalize
    /// ): returns a copy of string, with each first letter of a word in upper case.
    ///
    /// `S.capitalize()` returns a copy of string S with all Unicode letters
    /// that begin words changed to their title case.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "hello, world!".capitalize() == "Hello, World!"
    /// # )"#).unwrap());
    /// ```
    string.capitalize(this) {
        let mut last_space = true;
        let mut result = String::new();
        for c in this.to_str().chars() {
            if !c.is_alphanumeric() {
                last_space = true;
                result.push(c);
            } else {
                if last_space {
                    for c1 in c.to_uppercase() {
                        result.push(c1);
                    }
                } else {
                    result.push(c);
                }
                last_space = false;
            }
        }
        ok!(result)
    }

    /// [string.codepoints](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·codepoints
    /// ): returns an iterable of the unicode codepoint of a string.
    ///
    /// `S.codepoints()` returns an iterable value containing the
    /// sequence of integer Unicode code points encoded by the string S.
    /// Each invalid code within the string is treated as if it encodes the
    /// Unicode replacement character, U+FFFD.
    ///
    /// By returning an iterable, not a list, the cost of decoding the string
    /// is deferred until actually needed; apply `list(...)` to the result to
    /// materialize the entire sequence.
    ///
    /// Example:
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// list("Hello, 世界".codepoints()) == [72, 101, 108, 108, 111, 44, 32, 19990, 30028]
    /// # )"#).unwrap());
    /// ```
    string.codepoints(this) {
        // Note that we return a list here... Which is not equivalent to the go implementation.
        let v : Vec<i64> = this.to_str().chars().map(|x| u32::from(x) as i64).collect();
        ok!(v)
    }

    /// [string.count](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·count
    /// ): count the number of occurrences of a string in another string.
    ///
    /// `S.count(sub[, start[, end]])` returns the number of occcurences of
    /// `sub` within the string S, or, if the optional substring indices
    /// `start` and `end` are provided, within the designated substring of S.
    /// They are interpreted according to Skylark's [indexing conventions](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#indexing).
    ///
    /// This implementation does not count occurence of `sub` in the string `S`
    /// that overlap other occurence of S (which can happen if some suffix of S is a prefix of S).
    /// For instance, `"abababa".count("aba")` returns 2 for `[aba]a[aba]`, not counting the middle
    /// occurence: `ab[aba]ba` (this is following Python behavior).
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "hello, world!".count("o") == 2
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "abababa".count("aba") == 2
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "hello, world!".count("o", 7, 12) == 1  # in "world"
    /// # )"#).unwrap());
    /// ```
    string.count(this, #needle, start = 0, end = None) {
        check_string!(needle, count);
        convert_indices!(this, start, end);
        let this = this.to_str();
        let needle = needle.to_str();
        let n = needle.as_str();
        let mut counter = 0 as i64;
        let mut s = this.as_str().get(start..end).unwrap();
        loop {
            if let Some(offset) = s.find(n) {
                counter += 1;
                s = s.get(offset + n.len()..).unwrap_or("");
            } else {
                ok!(counter)
            }
        }
    }

    /// [string.endswith](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·endswith
    /// ): determine if a string ends with a given suffix.
    ///
    /// `S.endswith(suffix)` reports whether the string S has the specified suffix.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "filename.sky".endswith(".sky") == True
    /// # )"#).unwrap());
    /// ```
    string.endswith(this, #suffix) {
        check_string!(suffix, endswith);
        ok!(this.to_str().ends_with(suffix.to_str().as_str()))
    }

    /// [string.find](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·find
    /// ): find a substring in a string.
    ///
    /// `S.find(sub[, start[, end]])` returns the index of the first
    /// occurrence of the substring `sub` within S.
    ///
    /// If either or both of `start` or `end` are specified,
    /// they specify a subrange of S to which the search should be restricted.
    /// They are interpreted according to Skylark's [indexing conventions](#indexing).
    ///
    /// If no occurrence is found, `found` returns -1.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "bonbon".find("on") == 1
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".find("on", 2) == 4
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".find("on", 2, 5) == -1
    /// # )"#).unwrap());
    /// ```
    string.find(this, #needle, start = 0, end = None) {
        check_string!(needle, count);
        convert_indices!(this, start, end);
        let this = this.to_str();
        let needle = needle.to_str();
        if let Some(offset) = this.as_str().get(start..end).unwrap().find(needle.as_str()) {
            ok!((offset + start) as i64)
        } else {
            ok!(-1)
        }
    }

    /// [string.format](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·format
    /// ): format a string.
    ///
    /// `S.format(*args, **kwargs)` returns a version of the format string S
    /// in which bracketed portions `{...}` are replaced
    /// by arguments from `args` and `kwargs`.
    ///
    /// Within the format string, a pair of braces `{{` or `}}` is treated as
    /// a literal open or close brace.
    /// Each unpaired open brace must be matched by a close brace `}`.
    /// The optional text between corresponding open and close braces
    /// specifies which argument to use and how to format it, and consists of
    /// three components, all optional:
    /// a field name, a conversion preceded by '`!`', and a format specifier
    /// preceded by '`:`'.
    ///
    /// ```text
    /// {field}
    /// {field:spec}
    /// {field!conv}
    /// {field!conv:spec}
    /// ```
    ///
    /// The *field name* may be either a decimal number or a keyword.
    /// A number is interpreted as the index of a positional argument;
    /// a keyword specifies the value of a keyword argument.
    /// If all the numeric field names form the sequence 0, 1, 2, and so on,
    /// they may be omitted and those values will be implied; however,
    /// the explicit and implicit forms may not be mixed.
    ///
    /// The *conversion* specifies how to convert an argument value `x` to a
    /// string. It may be either `!r`, which converts the value using
    /// `repr(x)`, or `!s`, which converts the value using `str(x)` and is
    /// the default.
    ///
    /// The *format specifier*, after a colon, specifies field width,
    /// alignment, padding, and numeric precision.
    /// Currently it must be empty, but it is reserved for future use.
    ///
    /// Examples:
    ///
    /// ```rust
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "a{x}b{y}c{}".format(1, x=2, y=3) == "a2b3c1"
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "a{}b{}c".format(1, 2) == "a1b2c"
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "({1}, {0})".format("zero", "one") == "(one, zero)"
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Is {0!r} {0!s}?".format("heterological") == "Is \"heterological\" heterological?"
    /// # )"#).unwrap());
    /// ```
    string.format(this, *args, **kwargs) {
        let mut it = args.into_iter()?;
        let this = this.to_str();
        let mut captured_by_index = false;
        let mut captured_by_order = false;
        let mut result = String::new();
        let mut capture = String::new();
        for c in this.chars() {
            match (c, capture.as_str()) {
                ('{', "") | ('}', "") => capture.push(c),
                (.., "") => result.push(c),
                ('{', "{") => {
                    result.push('{');
                    capture.clear();
                },
                ('{', "}") => starlark_err!(
                    FORMAT_STRING_UNMATCHED_BRACKET_ERROR_CODE,
                    "Standalone '}' in format string".to_owned(),
                    "standalone '}'".to_owned()
                ),
                ('{', ..) => starlark_err!(
                    FORMAT_STRING_UNMATCHED_BRACKET_ERROR_CODE,
                    "Unmatched '{' in format string".to_owned(),
                    "unmatched '{'".to_owned()
                ),
                ('}', "}") => {
                    result.push('}');
                    capture.clear();
                },
                ('}', ..) => {
                    result += &format_capture(
                        &capture,
                        &mut it,
                        &mut captured_by_index,
                        &mut captured_by_order,
                        &args,
                        &kwargs)?;
                    capture.clear();
                },
                (.., "}") => starlark_err!(
                    FORMAT_STRING_UNMATCHED_BRACKET_ERROR_CODE,
                    "Standalone '}' in format string".to_owned(),
                    "standalone '}'".to_owned()
                ),
                _ => capture.push(c)
            }
        }
        match capture.as_str() {
            "}" => starlark_err!(
                FORMAT_STRING_UNMATCHED_BRACKET_ERROR_CODE,
                "Standalone '}' in format string".to_owned(),
                "standalone '}'".to_owned()
            ),
            "" => ok!(result),
            _ => starlark_err!(
                FORMAT_STRING_UNMATCHED_BRACKET_ERROR_CODE,
                "Unmatched '{' in format string".to_owned(),
                "unmatched '{'".to_owned()
            ),
        }

    }

    /// [string.index](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·index
    /// ): search a substring inside a string, failing on not found.
    ///
    /// `S.index(sub[, start[, end]])` returns the index of the first
    /// occurrence of the substring `sub` within S, like `S.find`, except
    /// that if the substring is not found, the operation fails.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "bonbon".index("on") == 1
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".index("on", 2) == 4
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".index("on", 2, 5) # error: substring not found  (in "nbo")
    /// # )"#).is_err());
    /// ```
    string.index(this, #needle, start = 0, end = None) {
        check_string!(needle, count);
        convert_indices!(this, start, end);
        let this = this.to_str();
        let needle = needle.to_str();
        if let Some(offset) = this.as_str().get(start..end).unwrap().find(needle.as_str()) {
            ok!((offset + start) as i64)
        } else {
            starlark_err!(
                SUBSTRING_INDEX_FAILED_ERROR_CODE,
                format!("Substring '{}' not found in '{}'", needle, this),
                "substring not found".to_owned()
            );
        }
    }

    /// [string.isalnum](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isalnum
    /// ): test if a string is composed only of letters and digits.
    ///
    /// `S.isalnum()` reports whether the string S is non-empty and consists only
    /// Unicode letters and digits.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "base64".isalnum() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Catch-22".isalnum() == False
    /// # )"#).unwrap());
    /// ```
    string.isalnum(this) {
        let this = this.to_str();
        if this.is_empty() {
            ok!(false);
        }
        for c in this.chars() {
            if !c.is_alphanumeric() {
                ok!(false);
            }
        }
        ok!(true);
    }

    /// [string.isalpha](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isalpha
    /// ): test if a string is composed only of letters.
    ///
    /// `S.isalpha()` reports whether the string S is non-empty and consists only of Unicode letters.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "ABC".isalpha() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Catch-22".isalpha() == False
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "".isalpha() == False
    /// # )"#).unwrap());
    /// ```
    string.isalpha(this) {
        let this = this.to_str();
        if this.is_empty() {
            ok!(false);
        }
        for c in this.chars() {
            if !c.is_alphabetic() {
                ok!(false);
            }
        }
        ok!(true);
    }

    /// [string.isdigit](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isdigit
    /// ): test if a string is composed only of digits.
    ///
    /// `S.isdigit()` reports whether the string S is non-empty and consists only of Unicode digits.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "123".isdigit() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Catch-22".isdigit() == False
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "".isdigit() == False
    /// # )"#).unwrap());
    /// ```
    string.isdigit(this) {
        let this = this.to_str();
        if this.is_empty() {
            ok!(false);
        }
        for c in this.chars() {
            if !c.is_numeric() {
                ok!(false);
            }
        }
        ok!(true);
    }

    /// [string.islower](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·islower
    /// ): test if all letters of a string are lowercase.
    ///
    /// `S.islower()` reports whether the string S contains at least one cased Unicode
    /// letter, and all such letters are lowercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "hello, world".islower() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Catch-22".islower() == False
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "123".islower() == False
    /// # )"#).unwrap());
    /// ```
    string.islower(this) {
        let mut result = false;
        for c in this.to_str().chars() {
            if c.is_uppercase() {
                ok!(false);
            } else if c.is_lowercase() {
                result = true;
            }
        }
        ok!(result);
    }

    /// [string.isspace](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isspace
    /// ): test if all characters of a string are whitespaces.
    ///
    /// `S.isspace()` reports whether the string S is non-empty and consists only of Unicode spaces.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "    ".isspace() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "\r\t\n".isspace() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "".isspace() == False
    /// # )"#).unwrap());
    /// ```
    string.isspace(this) {
        let this = this.to_str();
        if this.is_empty() {
            ok!(false);
        }
        for c in this.chars() {
            if !c.is_whitespace() {
                ok!(false);
            }
        }
        ok!(true);
    }

    /// [string.istitle](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·istitle
    /// ): test if the string is title cased.
    ///
    /// `S.istitle()` reports whether the string S contains at least one cased Unicode
    /// letter, and all such letters that begin a word are in title case.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "Hello, World!".istitle() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Catch-22".istitle() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "HAL-9000".istitle() == False
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "123".istitle() == False
    /// # )"#).unwrap());
    /// ```
    string.istitle(this) {
        let mut last_space = true;
        let mut result = false;

        for c in this.to_str().chars() {
            if !c.is_alphabetic() {
                last_space = true;
            } else {
                if last_space {
                    if c.is_lowercase() {
                        ok!(false);
                    }
                } else if c.is_uppercase() {
                    ok!(false);
                }
                if c.is_alphabetic() {
                    result = true;
                }
                last_space = false;
            }
        }
        ok!(result);
    }

    /// [string.isupper](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·isupper
    /// ): test if all letters of a string are uppercase.
    ///
    /// `S.isupper()` reports whether the string S contains at least one cased Unicode
    /// letter, and all such letters are uppercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "HAL-9000".isupper() == True
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "Catch-22".isupper() == False
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "123".isupper() == False
    /// # )"#).unwrap());
    /// ```
    string.isupper(this) {
        let mut result = false;
        for c in this.to_str().chars() {
            if c.is_lowercase() {
                ok!(false);
            } else if c.is_uppercase() {
                result = true;
            }
        }
        ok!(result);
    }

    /// [string.join](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·join
    /// ): join elements with a separator.
    ///
    /// `S.join(iterable)` returns the string formed by concatenating each
    /// element of its argument, with a copy of the string S between
    /// successive elements. The argument must be an iterable whose elements
    /// are strings.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// ", ".join(["one", "two", "three"]) == "one, two, three"
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "a".join("ctmrn".split_codepoints()) == "catamaran"
    /// # )"#).unwrap());
    /// ```
    string.join(this, #to_join) {
        let this = this.to_str();
        ok!(
            to_join.into_iter()?.fold(
                Ok(String::new()),
                |a, x| {
                    check_string!(x, join);
                    let a = a.unwrap();
                    if a.is_empty() {
                        Ok(x.to_str())
                    } else {
                        Ok(format!("{}{}{}", a, this, x.to_str()))
                    }
                }
            )?
        );
    }

    /// [string.lower](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·lower
    /// ): test if all letters of a string are lowercased.
    ///
    /// `S.lower()` returns a copy of the string S with letters converted to lowercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "Hello, World!".lower() == "hello, world!"
    /// # )"#).unwrap());
    /// ```
    string.lower(this) {
        ok!(this.to_str().to_lowercase())
    }

    /// [string.lstrip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·lstrip
    /// ): trim leading whitespaces.
    ///
    /// `S.lstrip()` returns a copy of the string S with leading whitespace removed.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "  hello  ".lstrip() == "hello  "
    /// # )"#).unwrap());
    /// ```
    string.lstrip(this) {
        ok!(this.to_str().trim_start())
    }

    /// [string.partition](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·partition
    /// ): partition a string in 3 components
    ///
    /// `S.partition(x = " ")` splits string S into three parts and returns them as
    /// a tuple: the portion before the first occurrence of string `x`, `x` itself,
    /// and the portion following it.
    /// If S does not contain `x`, `partition` returns `(S, "", "")`.
    ///
    /// `partition` fails if `x` is not a string, or is the empty string.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "one/two/three".partition("/")	 == ("one", "/", "two/three")
    /// # )"#).unwrap());
    /// ```
    string.partition(this, #needle = " ") {
        check_string!(needle, partition);
        let needle = needle.to_str();
        if needle.is_empty() {
            starlark_err!(
                INCORRECT_PARAMETER_TYPE_ERROR_CODE,
                "Empty separator cannot be used for partitioning".to_owned(),
                "Empty separtor".to_owned()
            )
        }
        let this = this.to_str();
        if let Some(offset) = this.find(needle.as_str()) {
            let offset2 = offset + needle.len();
            ok!((
                this.as_str().get(..offset).unwrap(),
                needle,
                this.as_str().get(offset2..).unwrap()
            ))
        } else {
            ok!((this, "", ""))
        }
    }

    /// [string.replace](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·replace
    /// ): replace all occurences of a subtring.
    ///
    /// `S.replace(old, new[, count])` returns a copy of string S with all
    /// occurrences of substring `old` replaced by `new`. If the optional
    /// argument `count`, which must be an `int`, is non-negative, it
    /// specifies a maximum number of occurrences to replace.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "banana".replace("a", "o")	 == "bonono"
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "banana".replace("a", "o", 2)	 == "bonona"
    /// # )"#).unwrap());
    /// ```
    string.replace(this, #old, #new, #count = None) {
        check_string!(old, replace);
        check_string!(new, replace);
        let (this, old, new) = (this.to_str(), old.to_str(), new.to_str());
        ok!(
            if count.get_type() == "NoneType" {
                this.replace(old.as_str(), new.as_str())
            } else {
                this.replacen(old.as_str(), new.as_str(), count.to_int()? as usize)
            }
        )
    }

    /// [string.rfind](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rfind
    /// ): find the last index of a substring.
    ///
    /// `S.rfind(sub[, start[, end]])` returns the index of the substring `sub` within
    /// S, like `S.find`, except that `rfind` returns the index of the substring's
    /// _last_ occurrence.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "bonbon".rfind("on") == 4
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".rfind("on", None, 5) == 1
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".rfind("on", 2, 5) == -1
    /// # )"#).unwrap());
    /// ```
    string.rfind(this, #needle, start = 0, end = None) {
        check_string!(needle, count);
        convert_indices!(this, start, end);
        let this = this.to_str();
        let needle = needle.to_str();
        if let Some(offset) = this.as_str().get(start..end).unwrap().rfind(needle.as_str()) {
            ok!((offset + start) as i64)
        } else {
            ok!(-1)
        }
    }

    /// [string.rindex](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rindex
    /// ): find the last index of a substring, failing on not found.
    ///
    /// `S.rindex(sub[, start[, end]])` returns the index of the substring `sub` within
    /// S, like `S.index`, except that `rindex` returns the index of the substring's
    /// _last_ occurrence.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "bonbon".rindex("on") == 4
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".rindex("on", None, 5) == 1  # in "bonbo"
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "bonbon".rindex("on", 2, 5)   # error: substring not found  (in "nbo")
    /// # )"#).is_err());
    /// ```
    string.rindex(this, #needle, start = 0, end = None) {
        check_string!(needle, count);
        convert_indices!(this, start, end);
        let this = this.to_str();
        let needle = needle.to_str();
        if let Some(offset) = this.as_str().get(start..end).unwrap().rfind(needle.as_str()) {
            ok!((offset + start) as i64)
        } else {
            starlark_err!(
                SUBSTRING_INDEX_FAILED_ERROR_CODE,
                format!("Substring '{}' not found in '{}'", needle, this),
                "substring not found".to_owned()
            );
        }
    }

    /// [string.rpartition](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rpartition
    /// ): partition a string in 3 elements.
    ///
    /// `S.rpartition([x = ' '])` is like `partition`, but splits `S` at the last occurrence of `x`.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "one/two/three".rpartition("/")	 == ("one/two", "/", "three")
    /// # )"#).unwrap());
    /// ```
    string.rpartition(this, #needle = " ") {
        check_string!(needle, partition);
        let needle = needle.to_str();
        if needle.is_empty() {
            starlark_err!(
                INCORRECT_PARAMETER_TYPE_ERROR_CODE,
                "Empty separator cannot be used for partitioning".to_owned(),
                "Empty separtor".to_owned()
            )
        }
        let this = this.to_str();
        if let Some(offset) = this.rfind(needle.as_str()) {
            let offset2 = offset + needle.len();
            ok!((
                this.as_str().get(..offset).unwrap(),
                needle,
                this.as_str().get(offset2..).unwrap()
            ))
        } else {
            ok!(("", "", this))
        }
    }

    /// [string.rsplit](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rsplit
    /// ): splits a string into substrings.
    ///
    /// `S.rsplit([sep[, maxsplit]])` splits a string into substrings like `S.split`,
    /// except that when a maximum number of splits is specified, `rsplit` chooses the
    /// rightmost splits.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "banana".rsplit("n") == ["ba", "a", "a"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "banana".rsplit("n", 1) == ["bana", "a"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "one two  three".rsplit(None, 1) == ["one two", "three"]
    /// # )"#).unwrap());
    /// ```
    string.rsplit(this, #sep = None, #maxsplit = None) {
        let this = this.to_str();
        let maxsplit = if maxsplit.get_type() == "NoneType" {
            None
        } else {
            let v = maxsplit.to_int()?;
            if v < 0 {
                None
            } else {
                Some((v + 1) as usize)
            }
        };
        if sep.get_type() == "NoneType" {
            if maxsplit.is_none() {
                let v : Vec<&str> = this.split_whitespace().collect();
                ok!(v)
            } else {
                ok!(rsplitn_whitespace(&this, maxsplit.unwrap()))
            }
        } else {
            check_string!(sep, split);
            let sep = sep.to_str();
            let mut v : Vec<&str> = if maxsplit.is_none() {
                this.rsplit(sep.as_str()).collect()
            } else {
                this.rsplitn(maxsplit.unwrap(), sep.as_str()).collect()
            };
            v.reverse();
            ok!(v)
        };
    }

    /// [string.rstrip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·rstrip
    /// ): trim trailing whitespace.
    ///
    /// `S.rstrip()` returns a copy of the string S with trailing whitespace removed.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "  hello  ".rstrip() == "  hello"
    /// # )"#).unwrap());
    /// ```
    string.rstrip(this) {
        ok!(this.to_str().trim_end())
    }

    /// [string.split](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·split
    /// ): split a string in substrings.
    ///
    /// `S.split([sep [, maxsplit]])` returns the list of substrings of S,
    /// splitting at occurrences of the delimiter string `sep`.
    ///
    /// Consecutive occurrences of `sep` are considered to delimit empty
    /// strings, so `'food'.split('o')` returns `['f', '', 'd']`.
    /// Splitting an empty string with a specified separator returns `['']`.
    /// If `sep` is the empty string, `split` fails.
    ///
    /// If `sep` is not specified or is `None`, `split` uses a different
    /// algorithm: it removes all leading spaces from S
    /// (or trailing spaces in the case of `rsplit`),
    /// then splits the string around each consecutive non-empty sequence of
    /// Unicode white space characters.
    ///
    /// If S consists only of white space, `split` returns the empty list.
    ///
    /// If `maxsplit` is given and non-negative, it specifies a maximum number of splits.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "one two  three".split() == ["one", "two", "three"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "one two  three".split(" ") == ["one", "two", "", "three"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "one two  three".split(None, 1) == ["one", "two  three"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "banana".split("n") == ["ba", "a", "a"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "banana".split("n", 1) == ["ba", "ana"]
    /// # )"#).unwrap());
    /// ```
    string.split(this, #sep = None, #maxsplit = None) {
        let this = this.to_str();
        let maxsplit = if maxsplit.get_type() == "NoneType" {
            None
        } else {
            let v = maxsplit.to_int()?;
            if v < 0 {
                None
            } else {
                Some((v + 1) as usize)
            }
        };
        let v : Vec<&str> =
            if sep.get_type() == "NoneType" {
                if maxsplit.is_none() {
                    this.split_whitespace().collect()
                } else {
                    ok!(splitn_whitespace(&this, maxsplit.unwrap()))
                }
            } else {
                check_string!(sep, split);
                let sep = sep.to_str();
                if maxsplit.is_none() {
                    this.split(sep.as_str()).collect()
                } else {
                    this.splitn(maxsplit.unwrap(), sep.as_str()).collect()
                }
            };
        ok!(v)
    }

    /// [string.split_codepoints](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·split_codepoints
    /// ): split a string into characters.
    ///
    /// `S.split_codepoints()` returns an iterable value containing the sequence of
    /// substrings of S that each encode a single Unicode code point.
    /// Each invalid code within the string is treated as if it encodes the
    /// Unicode replacement character, U+FFFD.
    ///
    /// By returning an iterable, not a list, the cost of decoding the string
    /// is deferred until actually needed; apply `list(...)` to the result to
    /// materialize the entire sequence.
    ///
    /// Example:
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// list("Hello, 世界".split_codepoints()) == ["H", "e", "l", "l", "o", ",", " ", "世", "界"]
    /// # )"#).unwrap());
    /// ```
    string.split_codepoints(this) {
        let v : Vec<String> = this.to_str().chars().map(|x| x.to_string()).collect();
        ok!(v)
    }

    /// [string.splitlines](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·splitlines
    /// ): return the list of lines of a string.
    ///
    /// `S.splitlines([keepends])` returns a list whose elements are the
    /// successive lines of S, that is, the strings formed by splitting S at
    /// line terminators ('\n', '\r' or '\r\n').
    ///
    /// The optional argument, `keepends`, is interpreted as a Boolean.
    /// If true, line terminators are preserved in the result, though
    /// the final element does not necessarily end with a line terminator.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "one\n\ntwo".splitlines() == ["one", "", "two"]
    /// # )"#).unwrap());
    /// # assert!(starlark_default(r#"(
    /// "one\n\ntwo".splitlines(True) == ["one\n", "\n", "two"]
    /// # )"#).unwrap());
    /// ```
    string.splitlines(this, #keepends = false) {
        check_type!(keepends, "string.splitlines", bool);
        let this = this.to_str();
        let mut s = this.as_str();
        let keepends = keepends.to_bool();
        let mut lines = Vec::new();
        loop {
            if let Some(x) = s.find(|x| x == '\n' || x == '\r') {
                let y = x;
                let x = match s.get(y..y+2) {
                    Some("\r\n") => y + 2,
                    _ => y + 1
                };
                if keepends {
                    lines.push(s.get(..x).unwrap())
                } else {
                    lines.push(s.get(..y).unwrap())
                }
                if x == s.len() {
                    ok!(lines);
                }
                s = s.get(x..).unwrap();
            } else {
                if !s.is_empty() {
                    lines.push(s);
                }
                ok!(lines);
            }
        }
    }

    /// [string.startswith](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·startswith
    /// ): test wether a string starts with a given prefix.
    ///
    /// `S.startswith(suffix)` reports whether the string S has the specified prefix.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "filename.sky".startswith("filename") == True
    /// # )"#).unwrap());
    /// ```
    string.startswith(this, #prefix) {
        check_string!(prefix, startswith);
        ok!(this.to_str().starts_with(prefix.to_str().as_str()))
    }

    /// [string.strip](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·strip
    /// ): trim leading and trailing whitespaces.
    ///
    /// `S.strip()` returns a copy of the string S with leading and trailing whitespace removed.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "  hello  ".strip() == "hello"
    /// # )"#).unwrap());
    /// ```
    string.strip(this) {
        ok!(this.to_str().trim())
    }

    /// [string.title](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·title
    /// ): convert a string to title case.
    ///
    /// `S.lower()` returns a copy of the string S with letters converted to titlecase.
    ///
    /// Letters are converted to uppercase at the start of words, lowercase elsewhere.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "hElLo, WoRlD!".title() == "Hello, World!"
    /// # )"#).unwrap());
    /// ```
    string.title(this) {
        let mut last_space = true;
        let mut result = String::new();
        for c in this.to_str().chars() {
            if  !c.is_alphabetic() {
                last_space = true;
                for c1 in c.to_lowercase() {
                    result.push(c1);
                }
            } else {
                if last_space {
                    for c1 in c.to_uppercase() {
                        result.push(c1);
                    }
                } else {
                    for c1 in c.to_lowercase() {
                        result.push(c1);
                    }
                }
                last_space = false;
            }
        }
        ok!(result);
    }

    /// [string.upper](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#string·upper
    /// ): convert a string to all uppercase.
    ///
    /// `S.lower()` returns a copy of the string S with letters converted to lowercase.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"(
    /// "Hello, World!".upper() == "HELLO, WORLD!"
    /// # )"#).unwrap());
    /// ```
    string.upper(this) {
        ok!(this.to_str().to_uppercase())
    }
}

#[cfg(test)]
mod tests {
    use super::super::starlark_default;
    use super::super::tests::starlark_default_fail;
    use super::*;
    use values::dict;

    macro_rules! starlark_ok {
        ($($t:expr),+) => (starlark_ok_fn!(starlark_default, $($t),+))
    }

    macro_rules! starlark_fail {
        ($($t:expr),+) => (starlark_fail_fn!(starlark_default_fail, $($t),+))
    }

    #[test]
    fn test_format_capture() {
        let args = Value::from(vec!["1", "2", "3"]);
        let mut kwargs = dict::Dictionary::new();
        let mut it = args.into_iter().unwrap();
        let mut captured_by_index = false;
        let mut captured_by_order = false;

        kwargs.set_at(Value::from("a"), Value::from("x")).unwrap();
        kwargs.set_at(Value::from("b"), Value::from("y")).unwrap();
        kwargs.set_at(Value::from("c"), Value::from("z")).unwrap();
        assert_eq!(
            format_capture(
                "{",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "1"
        );
        assert_eq!(
            format_capture(
                "{!s",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "2"
        );
        assert_eq!(
            format_capture(
                "{!r",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "\"3\""
        );
        assert_eq!(
            format_capture(
                "{a!r",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "\"x\""
        );
        assert_eq!(
            format_capture(
                "{a!s",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "x"
        );
        assert!(format_capture(
            "{1",
            &mut it,
            &mut captured_by_index,
            &mut captured_by_order,
            &args,
            &kwargs,
        )
        .is_err());
        captured_by_order = false;
        it = args.into_iter().unwrap();
        assert_eq!(
            format_capture(
                "{1",
                &mut it,
                &mut captured_by_index,
                &mut captured_by_order,
                &args,
                &kwargs,
            )
            .unwrap(),
            "2"
        );
        assert!(format_capture(
            "{",
            &mut it,
            &mut captured_by_index,
            &mut captured_by_order,
            &args,
            &kwargs,
        )
        .is_err());
    }

    #[test]
    fn test_elems() {
        starlark_ok!(
            r#"(list("Hello, 世界".elems()) == [
                            72, 101, 108, 108, 111, 44, 32, 228, 184, 150, 231, 149, 140])"#
        );
    }

    #[test]
    fn test_capitalize() {
        starlark_ok!(r#"("hello, world!".capitalize()	 == "Hello, World!")"#);
    }

    #[test]
    fn test_codepoints() {
        starlark_ok!(
            r#"(list("Hello, 世界".codepoints()) == [
                            72, 101, 108, 108, 111, 44, 32, 19990, 30028])"#
        );
    }

    #[test]
    fn test_count() {
        starlark_ok!(r#"("hello, world!".count("o") == 2)"#);
        starlark_ok!(r#"("abababa".count("aba") == 2)"#);
        starlark_ok!(r#"("hello, world!".count("o", 7, 12) == 1)"#);
    }

    #[test]
    fn test_endswith() {
        starlark_ok!(r#"("filename.sky".endswith(".sky") == True)"#);
    }

    #[test]
    fn test_find() {
        starlark_ok!(r#"("bonbon".find("on") == 1)"#);
        starlark_ok!(r#"("bonbon".find("on", 2) == 4)"#);
        starlark_ok!(r#"("bonbon".find("on", 2, 5) == -1)"#);
    }

    #[test]
    fn test_format() {
        starlark_ok!(r#"("a{x}b{y}c{}".format(1, x=2, y=3) == "a2b3c1")"#);
        starlark_ok!(r#"("a{}b{}c".format(1, 2) == "a1b2c")"#);
        starlark_ok!(r#"("({1}, {0})".format("zero", "one") == "(one, zero)")"#);
        starlark_ok!(
            r#"("Is {0!r} {0!s}?".format('heterological') ==
                    "Is \"heterological\" heterological?")"#
        );
    }

    #[test]
    fn test_index() {
        starlark_ok!(r#"("bonbon".index("on") == 1)"#);
        starlark_ok!(r#"("bonbon".index("on", 2) == 4)"#);
        starlark_fail!(
            r#""bonbon".index("on", 2, 5)"#,
            SUBSTRING_INDEX_FAILED_ERROR_CODE
        );
    }

    #[test]
    fn test_isalnum() {
        starlark_ok!(r#"("base64".isalnum() == True)"#);
        starlark_ok!(r#"("Catch-22".isalnum() == False)"#);
    }

    #[test]
    fn test_isalpha() {
        starlark_ok!(r#"("ABC".isalpha() == True)"#);
        starlark_ok!(r#"("Catch-22".isalpha() == False)"#);
        starlark_ok!(r#"("".isalpha() == False)"#);
    }

    #[test]
    fn test_isdigit() {
        starlark_ok!(r#"("123".isdigit() == True)"#);
        starlark_ok!(r#"("Catch-22".isdigit() == False)"#);
        starlark_ok!(r#"("".isdigit() == False)"#);
    }

    #[test]
    fn test_islower() {
        starlark_ok!(r#"("hello, world".islower() == True)"#);
        starlark_ok!(r#"("Catch-22".islower() == False)"#);
        starlark_ok!(r#"("123".islower() == False)"#);
    }

    #[test]
    fn test_isspace() {
        starlark_ok!(r#"("    ".isspace() == True)"#);
        starlark_ok!(r#"("\r\t\n".isspace() == True)"#);
        starlark_ok!(r#"("".isspace() == False)"#);
    }

    #[test]
    fn test_istitle() {
        starlark_ok!(r#"("Hello, World!".istitle() == True)"#);
        starlark_ok!(r#"("Catch-22".istitle() == True)"#);
        starlark_ok!(r#"("HAL-9000".istitle() == False)"#);
        starlark_ok!(r#"("123".istitle() == False)"#);
    }

    #[test]
    fn test_isupper() {
        starlark_ok!(r#"("HAL-9000".isupper() == True)"#);
        starlark_ok!(r#"("Catch-22".isupper() == False)"#);
        starlark_ok!(r#"("123".isupper() == False)"#);
    }

    #[test]
    fn test_join() {
        starlark_ok!(r#"(", ".join(["one", "two", "three"]) == "one, two, three")"#);
        starlark_ok!(r#"("a".join("ctmrn".split_codepoints()) == "catamaran")"#);
    }

    #[test]
    fn test_lower() {
        starlark_ok!(r#"("Hello, World!".lower() == "hello, world!")"#);
    }

    #[test]
    fn test_lstrip() {
        starlark_ok!(r#"("  hello  ".lstrip() == "hello  ")"#);
    }

    #[test]
    fn test_partition() {
        starlark_ok!(r#"("one/two/three".partition("/")	 == ("one", "/", "two/three"))"#);
    }

    #[test]
    fn test_replace() {
        starlark_ok!(r#"("banana".replace("a", "o")	 == "bonono")"#);
        starlark_ok!(r#"("banana".replace("a", "o", 2)	 == "bonona")"#);
    }

    #[test]
    fn test_rfind() {
        starlark_ok!(r#"("bonbon".rfind("on") == 4)"#);
        starlark_ok!(r#"("bonbon".rfind("on", None, 5) == 1)"#);
        starlark_ok!(r#"("bonbon".rfind("on", 2, 5) == -1)"#);
    }

    #[test]
    fn test_rindex() {
        starlark_ok!(r#"("bonbon".rindex("on") == 4)"#);
        starlark_ok!(r#"("bonbon".rindex("on", None, 5) == 1)"#);
        starlark_fail!(
            r#""bonbon".rindex("on", 2, 5)"#,
            SUBSTRING_INDEX_FAILED_ERROR_CODE
        );
    }

    #[test]
    fn test_rpartition() {
        starlark_ok!(r#"("one/two/three".rpartition("/") == ("one/two", "/", "three"))"#);
    }

    #[test]
    fn test_rsplit() {
        starlark_ok!(r#"("banana".rsplit("n") == ["ba", "a", "a"])"#);
        starlark_ok!(r#"("banana".rsplit("n", 1) == ["bana", "a"])"#);
        starlark_ok!(r#"("one two  three".rsplit(None, 1) == ["one two", "three"])"#);
    }

    #[test]
    fn test_rstrip() {
        starlark_ok!(r#"("  hello  ".rstrip() == "  hello")"#);
    }

    #[test]
    fn test_split() {
        starlark_ok!(r#"("one two  three".split() == ["one", "two", "three"])"#);
        starlark_ok!(r#"("one two  three".split(" ") == ["one", "two", "", "three"])"#);
        starlark_ok!(r#"("one two  three".split(None, 1) == ["one", "two  three"])"#);
        starlark_ok!(r#"("banana".split("n") == ["ba", "a", "a"])"#);
        starlark_ok!(r#"("banana".split("n", 1) == ["ba", "ana"])"#);
    }

    #[test]
    fn test_split_codepoints() {
        starlark_ok!(r#"(list('Hello, 世界'.split_codepoints()) == ['H', 'e', 'l', 'l', 'o', ',', ' ', '世', '界'])"#);
    }

    #[test]
    fn test_splitlines() {
        starlark_ok!(r#"("one\n\ntwo".splitlines() == ["one", "", "two"])"#);
        starlark_ok!(r#"("one\n\ntwo".splitlines(True) == ["one\n", "\n", "two"])"#);
        starlark_ok!(r#"("a\nb".splitlines() == ["a", "b"])"#);
    }

    #[test]
    fn test_startswith() {
        starlark_ok!(r#"("filename.sky".startswith("filename") == True)"#);
    }

    #[test]
    fn test_strip() {
        starlark_ok!(r#"("  hello  ".strip() == "hello")"#);
    }

    #[test]
    fn test_title() {
        starlark_ok!(r#"("hElLo, WoRlD!".title() == "Hello, World!")"#);
    }

    #[test]
    fn test_upper() {
        starlark_ok!(r#"("Hello, World!".upper() == "HELLO, WORLD!")"#);
    }
}
