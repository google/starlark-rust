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

use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use starlark::eval::interactive::{eval, eval_file, EvalError};
use starlark::stdlib::global_environment_with_extensions;
use starlark::syntax::ast::AstStatement;
use starlark::syntax::dialect::Dialect;
use starlark::syntax::parser::{parse, parse_file};
use starlark::values::Value;
use starlark_repl::{print_function, repl};
use std::process::exit;
use std::sync::{Arc, Mutex};
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
    #[structopt(short = "a", long, help = "Parse and print AST instead of evaluating.")]
    ast: bool,

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

    #[structopt(name = "FILE", help = "Files to interpret")]
    files: Vec<String>,
}

fn main() {
    let opt = Opt::from_args();

    let command = opt.command;
    let ast = opt.ast;

    let global = print_function(global_environment_with_extensions());
    global.freeze();

    let dialect = if opt.build_file {
        Dialect::Build
    } else {
        Dialect::Bzl
    };
    let free_args_empty = opt.files.is_empty();
    for i in opt.files.into_iter() {
        if ast {
            let codemap = Arc::new(Mutex::new(CodeMap::new()));
            maybe_print_ast_or_exit(parse_file(&codemap, &i, dialect), &codemap);
        } else {
            maybe_print_or_exit(eval_file(
                &i,
                dialect,
                &mut global.child(&i),
                global.clone(),
            ));
        }
    }
    if opt.repl || (free_args_empty && command.is_none()) {
        println!("Welcome to Starlark REPL, press Ctrl+D to exit.");
        repl(&global, dialect, ast);
    }
    if let Some(command) = command {
        let path = "[command flag]";
        if ast {
            let codemap = Arc::new(Mutex::new(CodeMap::new()));
            maybe_print_ast_or_exit(parse(&codemap, path, &command, dialect), &codemap);
        } else {
            maybe_print_or_exit(eval(
                "[command flag]",
                &command,
                dialect,
                &mut global.child("[command flag]"),
                global.clone(),
            ));
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
