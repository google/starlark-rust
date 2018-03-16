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

//! Test the conformance tests from other implementation of Starlark
extern crate starlark;
extern crate codemap;
extern crate codemap_diagnostic;

use std::fs::File;
use std::path::Path;
use std::io::{self, Write};
use std::io::prelude::*;
use starlark::stdlib::global_environment;
use starlark::eval::simple::eval;
use std::sync::{Arc, Mutex};
use codemap::CodeMap;
use codemap_diagnostic::{Emitter, ColorConfig};

/// Load a file and convert it to a vector of string (separated by ---) to be evaluated separately.
fn read_input(path: &str) -> Vec<String> {
    let mut content = String::new();
    let mut file = File::open(path).unwrap();
    file.read_to_string(&mut content).unwrap();
    content.split("\n---\n").map(|x| x.to_owned()).collect()
}

fn run_conformance_test(path: &str) -> bool {
    let map = Arc::new(Mutex::new(CodeMap::new()));
    let mut offset = 0;
    let global = global_environment();
    global.freeze();
    let mut prelude = global.child("PRELUDE");
    eval(&map, "PRELUDE", r#"
def assert_eq(x, y):
  if x != y:
    fail("%r != %r" % (x, y))

def assert_(cond, msg="assertion failed"):
  if not cond:
    fail(msg)
"#, false, &mut prelude).unwrap();
    prelude.freeze();
    for content in read_input(path) {
        let err = if let Some(x) = content.find("###") {
            let err = content.get(x+3..).unwrap().trim();
            err.get(..err.find("\n").unwrap_or(err.len())).unwrap()
        } else { "" };
        match eval(
            &map,
            &format!("{}<{}>", path, offset),
            &content,
            false,
            &mut prelude.child(&path)
        ) {
            Err(p) => {
                if err.is_empty() {
                    Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
                    return false;
                } else {
                    if !p.message.contains(err) {
                        io::stderr().write(&format!(
                            "Expected error '{}' at {}:{}, got {}\n",
                            err,
                            path,
                            offset,
                            p.message,
                        ).into_bytes()).unwrap();
                        Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
                        return false;
                    }
                }
            },
            _ => {
                if !err.is_empty() {
                    io::stderr().write(&format!(
                        "Expected error '{}' at {}:{}, got success",
                        err,
                        path,
                        offset,
                    ).into_bytes()).unwrap();
                    return false;
                }
            }
        }
        offset += content.len() + 5; // + 5 for "\n---\n"
    }
    return true;
}

fn do_conformance_test(path: &str) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
    assert!(run_conformance_test(path.to_str().unwrap()));
}

include!(concat!(env!("OUT_DIR"), "/tests/testcases.rs"));
