// Copyright 2019 The Starlark in Rust Authors
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

//! Refcounted string,

use crate::values::inspect::Inspectable;
use crate::values::Value;
use crate::values::ValueInner;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::{fmt, ops};

/// Refcounted string.
///
/// Newtype to avoid rewriting a lot of code when implementation changes.
#[derive(Eq, PartialEq, PartialOrd, Ord, Clone)]
// Note `None` is empty string and `Some("")` is not permitted,
// otherwise derives won't work correctly
pub struct RcString(Option<Rc<String>>);

impl Borrow<str> for RcString {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

/// Note `Hash` must be compatible with [`str`], otherwise
/// `HashMap` query by `str` won't work correctly.
impl Hash for RcString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl ops::Deref for RcString {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

static EMPTY_STRING: String = String::new();

impl RcString {
    /// Useful for downcasting
    pub(crate) fn as_string(&self) -> &String {
        match &self.0 {
            Some(s) => s,
            None => &EMPTY_STRING,
        }
    }

    pub fn as_str(&self) -> &str {
        self.as_string().as_str()
    }
}

impl fmt::Display for RcString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl fmt::Debug for RcString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.as_str(), f)
    }
}

impl<I: Into<String>> From<I> for RcString {
    fn from(s: I) -> Self {
        let s = s.into();
        if s.is_empty() {
            RcString(None)
        } else {
            RcString(Some(Rc::new(s)))
        }
    }
}

impl From<RcString> for Value {
    fn from(s: RcString) -> Self {
        Value(ValueInner::String(s))
    }
}

impl Inspectable for RcString {
    fn inspect(&self) -> Value {
        Value::from(self.clone())
    }
}

#[cfg(test)]
mod test {
    use crate::values::string::rc::RcString;
    use std::borrow::Borrow;

    #[test]
    fn eq() {
        assert_eq!(RcString::from("ab"), RcString::from("ab"))
    }

    #[test]
    fn from() {
        assert_eq!("ab", format!("{}", RcString::from("ab")));
        assert_eq!("ab", format!("{}", RcString::from("ab".to_owned())));
    }

    #[test]
    fn borrow() {
        assert_eq!("ab", Borrow::<str>::borrow(&RcString::from("ab")));
    }
}
