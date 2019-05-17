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

//! A command line interpreter for Starlark, provide a REPL.

use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use getopts::Options;
use starlark::eval::interactive::{eval, eval_file, EvalError};
use starlark::stdlib::{global_environment, structs};
use starlark::syntax::ast::AstStatement;
use starlark::syntax::dialect::Dialect;
use starlark::syntax::parser::{parse, parse_file};
use starlark::values::Value;
use starlark_repl::{print_function, repl};
use std::env;
use std::process::exit;
use std::sync::{Arc, Mutex};

const EXIT_CODE_USAGE: i32 = 1;
const EXIT_CODE_FAILURE: i32 = 2;

macro_rules! print_usage {
    ($program: expr, $opts: expr) => (
        {
            let brief = format!("[Starlark in Rust interpretor]

Usage: {} [options] [file1..filen]
", $program);
            eprint!("{}", $opts.usage(&brief));
        }
    );
    ($program: expr, $opts: expr, $($fmt:expr),+) => (
        {
            print_usage!($program, $opts);
            eprintln!($($fmt),+);
        }
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let program = args[0].clone();

    let mut opts = Options::new();
    opts.optflag(
        "b",
        "build_file",
        concat!(
            "Parse the build file format instead of full Starlark. See https://docs.rs/starlark/",
            env!("CARGO_PKG_VERSION"),
            "/starlark/eval/index.html#build_file"
        ),
    );
    opts.optflag("h", "help", "Show the usage of this program.");
    opts.optflag("r", "repl", "Run a REPL after files have been parsed.");
    opts.optflag("a", "ast", "Parse and print AST instead of evaluating");
    opts.optopt(
        "c",
        "command",
        "Starlark command to run after files have been parsed.",
        "expr",
    );
    match opts.parse(&args[1..]) {
        Err(e) => {
            print_usage!(program, opts, "\n{}\n", e);
        }
        Ok(matches) => {
            if matches.opt_present("h") {
                print_usage!(program, opts);
            } else {
                let build_file = matches.opt_present("b");
                let opt_repl = matches.opt_present("r");
                let command = matches.opt_str("c");
                let ast = matches.opt_present("a");

                if opt_repl && command.is_some() {
                    eprintln!("Cannot pass both -r and -c");
                    exit(EXIT_CODE_USAGE);
                }

                let global = print_function(global_environment());
                // `struct` is not a part of the Starlark spec, but may be useful in REPL.
                let global = structs::global(global);
                global.freeze();

                let dialect = if build_file {
                    Dialect::Build
                } else {
                    Dialect::Bzl
                };
                let free_args_empty = matches.free.is_empty();
                for i in matches.free.into_iter() {
                    if ast {
                        let codemap = Arc::new(Mutex::new(CodeMap::new()));
                        maybe_print_ast_or_exit(parse_file(&codemap, &i, dialect), &codemap);
                    } else {
                        maybe_print_or_exit(eval_file(&i, dialect, &mut global.child(&i)));
                    }
                }
                if opt_repl || (free_args_empty && command.is_none()) {
                    println!("Welcome to Starlark REPL, press Ctrl+D to exit.");
                    repl(&global, dialect, ast);
                }
                if let Some(command) = command {
                    let path = "[command flag]";
                    if ast {
                        let codemap = Arc::new(Mutex::new(CodeMap::new()));
                        maybe_print_ast_or_exit(parse(&codemap, path, &command, dialect), &codemap);
                    } else {
                        maybe_print_or_exit(eval(path, &command, dialect, &mut global.child(path)));
                    }
                }
            }
        }
    }
}

fn maybe_print_ast_or_exit(
    result: Result<AstStatement, Diagnostic>,
    codemap: &Arc<Mutex<CodeMap>>,
) {
    match result {
        Ok(ast) => {
            println!("{:#?}", ast);
        }
        Err(diagnostic) => {
            Emitter::stderr(ColorConfig::Auto, Some(&*codemap.lock().unwrap())).emit(&[diagnostic]);
            exit(EXIT_CODE_FAILURE);
        }
    }
}

fn maybe_print_or_exit(result: Result<Option<Value>, EvalError>) {
    match result {
        Ok(Some(value)) => println!("{}", value.to_repr()),
        Err(err) => {
            err.write_to_stderr();
            exit(EXIT_CODE_FAILURE);
        }
        Ok(None) => {}
    }
}
