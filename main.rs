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

extern crate getopts;

use getopts::Options;
use std::env;

macro_rules! print_usage {
    ($program: expr, $opts: expr) => (
        {
            let brief = format!("[Rust Starlark evaluator]

Usage: {} command [options] [arg1..argn]

Available commands:
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

    let /* mut */ opts = Options::new();
    let matches = opts.parse(&args[1..]).unwrap();
    let command = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage!(&program, opts);
        return;
    };
    match &command[..] {
        cmd => print_usage!(program, opts, "Invalid command: {}", cmd)
    }
}
