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
//! Starlark call stack.

use std::fmt;

/// Starlark call stack.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct CallStack {
    stack: Vec<(String, String)>,
}

impl CallStack {
    /// Push an element to the stack
    pub fn push(&mut self, function_id: &str, call_descr: &str, file_name: &str, line: u32) {
        self.stack.push((
            function_id.to_owned(),
            format!(
                "call to {} at {}:{}",
                call_descr,
                file_name,
                line + 1, // line 1 is 0, so add 1 for human readable.
            ),
        ));
    }

    /// Test if call stack contains a function with given id.
    pub fn contains(&self, function_id: &str) -> bool {
        self.stack.iter().any(|(n, _)| n == function_id)
    }

    /// Print call stack as multiline string
    /// with each line beginning with newline.
    pub fn print_with_newline_before<'a>(&'a self) -> impl fmt::Display + 'a {
        DisplayWithNewlineBefore { call_stack: self }
    }
}

struct DisplayWithNewlineBefore<'a> {
    call_stack: &'a CallStack,
}

impl<'a> fmt::Display for DisplayWithNewlineBefore<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (_fname, descr) in self.call_stack.stack.iter().rev() {
            write!(f, "\n    {}", descr)?;
        }
        Ok(())
    }
}
