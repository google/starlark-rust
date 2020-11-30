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

extern crate structopt;

use starlark::eval::interactive::{eval, eval_file, EvalError};
use starlark::stdlib::global_environment_for_repl_and_tests;
use starlark::syntax::dialect::Dialect;
use starlark::values::Value;
use starlark_repl::{print_function, repl};
use std::path::{Path, PathBuf};
use std::process::exit;
use structopt::clap::AppSettings;
use structopt::StructOpt;

const EXIT_CODE_FAILURE: i32 = 2;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "starlark-repl",
    about = "Starlark in Rust interpreter",
    global_settings(&[AppSettings::ColoredHelp]),
)]
pub struct Opt {
    #[structopt(
        short = "b",
        long,
        help = concat!(
            "Parse the build file format instead of full Starlark. See https://docs.rs/starlark/",
            env!("CARGO_PKG_VERSION"),
            "/starlark/eval/index.html#build_file",
        )
    )]
    build_file: bool,

    #[structopt(
        short = "c",
        help = "Starlark command to run after files have been parsed."
    )]
    command: Option<String>,

    #[structopt(
        short = "r",
        long,
        conflicts_with = "command",
        help = "Run a REPL after files have been parsed."
    )]
    repl: bool,

    #[structopt(name = "FILE", help = "Files to interpret", parse(from_os_str))]
    files: Vec<PathBuf>,
}

fn main() {
    let opt = Opt::from_args();

    let command = opt.command;

    let (mut global, mut type_values) = global_environment_for_repl_and_tests();

    print_function(&mut global, &mut type_values);
    global.freeze();

    let dialect = if opt.build_file {
        Dialect::Build
    } else {
        Dialect::Bzl
    };
    let free_args_empty = opt.files.is_empty();
    for i in opt.files.into_iter() {
        maybe_print_or_exit(eval_file(
            &i,
            dialect,
            &mut global.child(i.to_string_lossy().as_ref()),
            &type_values,
            global.clone(),
        ));
    }
    if opt.repl || (free_args_empty && command.is_none()) {
        println!("Welcome to Starlark REPL, press Ctrl+D to exit.");
        repl(&mut global, &type_values, dialect);
    }
    if let Some(command) = command {
        maybe_print_or_exit(eval(
            Path::new("[command flag]"),
            &command,
            dialect,
            &mut global.child("[command flag]"),
            &type_values,
            global.clone(),
        ));
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
