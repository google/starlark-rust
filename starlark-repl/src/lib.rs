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

//! a Read-Eval-Print Loop (REPL) for Starlark.
//!
//! Starlark, formerly codenamed Skylark, is a non-Turing complete language based on Python that
//! was made for the [Bazel build system](https://bazel.build) to define compilation plugin.
//!
//! See the [starlark](https://docs.rs/crate/starlark) crate documentation for more information
//! about Starlark.
//!
//! # Usage
//!
//! One can call the [repl] method to run the repl inside a program or simply run the [starlark-repl]
//! binary:
//!  ```sh
//! $ starlark-repl --help
//! [Starlark in Rust interpretor]
//!
//! Usage: starlark-repl [options] [file1..filen]
//!
//!
//! Options:
//!     -b, --build_file    Parse the build file format instead of full Starlark.
//!     -h, --help          Show the usage of this program.
//!     -r, --repl          Run a REPL after files have been parsed.
//! ```
use codemap;

#[macro_use]
extern crate starlark;

use codemap_diagnostic::{ColorConfig, Emitter};
use linefeed::{Interface, ReadResult};
use starlark::environment::Environment;
use starlark::eval::eval_lexer;
use starlark::eval::simple::SimpleFileLoader;
use starlark::syntax::dialect::Dialect;
use starlark::syntax::lexer::{BufferedLexer, LexerIntoIter, LexerItem};
use starlark::values::Value;
use std::env;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

fn print_eval<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>>(
    map: Arc<Mutex<codemap::CodeMap>>,
    filename: &str,
    content: &str,
    lexer: T2,
    dialect: Dialect,
    env: &mut Environment,
) {
    match eval_lexer(
        &map,
        filename,
        content,
        dialect,
        lexer,
        env,
        SimpleFileLoader::new(&map.clone()),
    ) {
        Ok(v) => {
            if v.get_type() != "NoneType" {
                println!("{}", v.to_repr())
            }
        }
        Err(p) => Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]),
    }
}

starlark_module! {print_function =>
    /// print: print an object string representation to stderr.
    ///
    /// Examples:
    /// ```python
    /// print("some message")  # Will print "some message" to stderr
    /// ```
    print(*args) {
        let mut r = String::new();
        let mut first = true;
        for arg in args.iter()? {
            if !first {
                r.push_str(" ");
            }
            first = false;
            r.push_str(&arg.to_str());
        }
        eprintln!("{}", r);
        Ok(Value::new(None))
    }
}

/// A REPL (Read-Eval-Print Loop) for Starlark.
///
/// This method run a REPL until the user hit Ctrl+D. It can be used for interactive use where the
/// parent enviroment offer side-effect methods.
///
/// # Parameters:
///
/// * global_environment: the parent enviroment for the loop.
/// * dialect: Starlark language dialect.
pub fn repl(global_environment: &Environment, dialect: Dialect) {
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    let reader = Interface::new("Starlark").unwrap();
    let mut env = global_environment.child("repl");
    let mut n = 0;

    // Linefeed default history size is unlimited,
    // but since we write history to disk, we better limit it.
    reader.set_history_size(100_000);

    let histfile = env::var_os("STARLARK_RUST_HISTFILE").map(PathBuf::from);

    if let Some(ref histfile) = histfile {
        if histfile.exists() {
            if let Err(e) = reader.load_history(histfile) {
                eprintln!("Failed to load history from {}: {}", histfile.display(), e);
            }
        }
    }

    reader.set_prompt(">>> ").unwrap();

    while let Ok(ReadResult::Input(input)) = reader.read_line() {
        if !input.is_empty() {
            reader.set_prompt("... ").unwrap();
            n += 1;
            let input = input + "\n";
            let mut lexer = BufferedLexer::new(&input);
            let mut content = input;
            while lexer.need_more() {
                if let Ok(ReadResult::Input(input)) = reader.read_line() {
                    let input = input + "\n";
                    content += &input;
                    lexer.input(&input);
                } else {
                    break;
                }
            }
            let mut hist = content.clone();
            hist.pop();
            reader.add_history(hist);
            print_eval(
                map.clone(),
                &format!("<{}>", n),
                &content,
                lexer,
                dialect,
                &mut env,
            )
        }
        reader.set_prompt(">>> ").unwrap();
    }

    println!();

    if let Some(ref histfile) = histfile {
        if let Err(e) = reader.save_history(histfile) {
            eprintln!("Failed to save history to {}: {}", histfile.display(), e);
        }
    }

    println!("Goodbye!");
}
