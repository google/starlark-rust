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

extern crate getopts;
extern crate starlark;

use getopts::Options;
use starlark::eval::interactive::eval_file;
use starlark::eval::repl::repl;
use starlark::stdlib::global_environment;
use std::env;

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
        "Parse the build file format instead of full Starlark.",
    );
    opts.optflag("h", "help", "Show the usage of this program.");
    opts.optflag("r", "repl", "Run a REPL after files have been parsed.");
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
                let global = global_environment();
                global.freeze();
                for i in matches.free.into_iter() {
                    eval_file(&i, build_file, &mut global.child(&i));
                }
                if opt_repl {
                    println!("Welcome to Starlark REPL, press Ctrl+D to exit.");
                    repl(&global, build_file);
                }
            }
        }
    }
}
