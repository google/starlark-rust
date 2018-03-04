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
extern crate starlark;
extern crate codemap;
extern crate codemap_diagnostic;
extern crate linefeed;

use getopts::Options;
use std::env;
use std::sync::{Arc, Mutex};
use starlark::syntax::lexer::{LexerIntoIter, BufferedLexer, Lexer, LexerItem};
use starlark::syntax::parser::{parse_lexer, parse_file};
use starlark::syntax::errors::SyntaxError;
use starlark::environment::Environment;
use starlark::values::TypedValue;
use starlark::eval::{eval_file, eval_lexer};
use std::fs::File;
use std::io::Read;
use codemap_diagnostic::{ColorConfig, Emitter};
use linefeed::{Reader, ReadResult};

fn print_lexing<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>>(
    map: Arc<Mutex<codemap::CodeMap>>,
    filename: &str,
    content: &str,
    show_span: bool,
    lexer: T2,
) {
    let mut map = map.lock().unwrap();
    let file_map = map.add_file(filename.to_owned(), content.to_owned());
    let mut emitter = Emitter::stderr(ColorConfig::Always, Some(&map));
    for r in lexer.into_iter() {
        match r {
            Ok((i, t, j)) => {
                if show_span {
                    println!("{}> {:?} <{}", i, t, j)
                } else {
                    println!("{:?}", t)
                }
            }
            Err(x) => emitter.emit(&[x.to_diagnostic(file_map.span)]),
        }
    }
}

fn lex(filename: &str, show_span: bool) {
    let mut content = String::new();
    let mut file = File::open(filename).unwrap();
    file.read_to_string(&mut content).unwrap();
    let content2 = content.clone();
    let lexer = Lexer::new(&content2);
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    print_lexing(map, filename, &content, show_span, lexer);
}

fn print_ast<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>>(
    map: Arc<Mutex<codemap::CodeMap>>,
    filename: &str,
    content: &str,
    lexer: T2,
    build: bool,
    show_span: bool,
) {
    match parse_lexer(&map, filename, content, build, lexer) {
        Ok(s) => {
            if show_span {
                println!("{:?}> {} <{:?}", s.span.low(), s.node, s.span.high())
            } else {
                println!("{}", s.node)
            }
        }
        Err(p) => Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]),
    }
}

fn ast(filename: &str, build_file: bool, show_span: bool) {
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    match parse_file(&map, filename, build_file) {
        Ok(s) => {
            if show_span {
                println!("{:?}> {} <{:?}", s.span.low(), s.node, s.span.high())
            } else {
                println!("{}", s.node)
            }
        }
        Err(x) => Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[x]),
    }
}

fn print_eval<T1: Iterator<Item = LexerItem>, T2: LexerIntoIter<T1>>(
    map: Arc<Mutex<codemap::CodeMap>>,
    filename: &str,
    content: &str,
    lexer: T2,
    build: bool,
    env: &mut Environment,
) {
    match eval_lexer(&map, filename, content, build, lexer, env) {
        Ok(v) => {
            if v.get_type() != "NoneType" {
                println!("{}", v.to_repr())
            }
        }
        Err(p) => Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]),
    }
}

fn eval(filename: &str, build_file: bool) {
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    // TODO: expose that environment? We don't need it for now as file parameters are just
    // evaluated and result is discarded.
    let mut env = Environment::new(filename);
    match eval_file(&map, filename, build_file, &mut env) {
        Ok(v) => {
            if v.get_type() != "NoneType" {
                println!("{}", v.to_repr())
            }
        }
        Err(p) => Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]),
    }
}

fn repl(build_file: bool, mode: &str, show_span: bool) {
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    let mut reader = Reader::new("Starlark").unwrap();
    let mut env = Environment::new("repl");
    let mut n = 0;

    println!("Welcome to Starlark REPL, press Ctrl+D to exit.");
    reader.set_prompt(">>> ");

    while let Ok(ReadResult::Input(input)) = reader.read_line() {
        if input.len() != 0 {
            reader.set_prompt("... ");
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
            match mode {
                "lex" => print_lexing(map.clone(), &format!("<{}>", n), &content, show_span, lexer),
                "ast" => {
                    print_ast(
                        map.clone(),
                        &format!("<{}>", n),
                        &content,
                        lexer,
                        build_file,
                        show_span,
                    )
                }
                "eval" => {
                    print_eval(
                        map.clone(),
                        &format!("<{}>", n),
                        &content,
                        lexer,
                        build_file,
                        &mut env,
                    )
                }
                _ => panic!("Invalid mode {}", mode),
            }

        }
        reader.set_prompt(">>> ")
    }
    println!("\nGoodbye!");
}

macro_rules! print_usage {
    ($program: expr, $opts: expr) => (
        {
            let brief = format!("[Rust Starlark evaluator]

Usage: {} command [options] [file1..filen]
", $program);
            eprint!("{}

Available modes (for --mode):
  lex: parse the starlark code and return the list of lexical tokens
  ast: generate the ASTs from the starlark code
  eval: do the full evaluation of the starlark code
", $opts.usage(&brief));
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
        "Parse the build file format instead of full Starlark",
    );
    opts.optopt(
        "m",
        "mode",
        "Specify which mode to run in, default is eval.",
        "[lex|ast|eval]",
    );
    opts.optflag("r", "repl", "Run a REPL after files have been parsed.");
    opts.optflag(
        "s",
        "show_span",
        "Show spanning of elements when displaying AST / Lexical token",
    );
    let matches = opts.parse(&args[1..]).unwrap();
    let build_file = matches.opt_present("b");
    let opt_repl = matches.opt_present("r");
    let show_span = matches.opt_present("s");
    let mode = matches.opt_str("m").unwrap_or("eval".to_owned());
    match mode.as_str() {
        "lex" | "ast" | "eval" => (),
        _ => {
            print_usage!(&program, opts);
            return ();
        }
    }
    for i in matches.free.into_iter() {
        match mode.as_str() {
            "lex" => lex(&i, show_span),
            "ast" => ast(&i, build_file, show_span),
            "eval" => eval(&i, build_file),
            _ => panic!("Invalid mode {}", mode),
        }
    }
    if opt_repl {
        repl(build_file, &mode, show_span)
    }
}
