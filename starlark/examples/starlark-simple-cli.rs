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

//! An example binary demonstrating how to use the starlark-rust crate.
//!
//! This program demonstrates how to set up a `codemap` and `Environment` required for
//! `eval()`, as well as how to use [values](values) returned by `eval()`. It accepts
//! a Starlark program on standard input and prints the result if the result is a string.

extern crate codemap;
extern crate codemap_diagnostic;
extern crate starlark;

use std::io::{self, Read};
use std::process::exit;
use std::sync::{Arc, Mutex};

use codemap_diagnostic::{ColorConfig, Emitter};
use starlark::eval::simple::eval;
use starlark::stdlib::global_environment;
use starlark::syntax::dialect::Dialect;

pub fn simple_evaluation(starlark_input: &String) -> Result<String, String> {
    // Create a new global environment populated with the stdlib.
    let global_env = global_environment();
    // Extra symbols can be added to the global environment before freezing if desired.
    global_env.freeze();
    // Create our own local copy of the global environment.
    let mut env = global_env.child("simple-cli");

    // Create a codemap to record the raw source of all code executed, including code
    // introduced by a Starlark load() call.
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));

    // We don't have a filename since we're not reading from a file, so call it "stdin".
    let result = eval(
        &map,
        "stdin",
        &starlark_input,
        Dialect::Bzl,
        &mut env,
        global_env.clone(),
    );

    match result {
        Ok(res) => match res.get_type() {
            "string" => Ok(res.to_str()),
            _ => Err(format!(
                "Error interpreting '{}': result must be string! (was {})",
                starlark_input,
                res.get_type()
            )),
        },
        Err(diagnostic) => {
            // Get the lock to the codemap and unlock it so we can use it.
            let cloned_map_lock = Arc::clone(&map);
            let unlocked_map = cloned_map_lock.lock().unwrap();

            // Emit code diagnostic information to standard error.
            Emitter::stderr(ColorConfig::Always, Some(&unlocked_map)).emit(&[diagnostic]);
            Err(format!("Error interpreting '{}'", starlark_input))
        }
    }
}

fn main() {
    let mut starlark_input = String::new();
    io::stdin()
        .read_to_string(&mut starlark_input)
        .expect("Error reading from stdin");
    let starlark_input = starlark_input.trim().to_owned();

    match simple_evaluation(&starlark_input) {
        Ok(result_string) => println!("{}", result_string),
        Err(error_string) => {
            println!("{}", error_string);
            exit(2);
        }
    }
}
