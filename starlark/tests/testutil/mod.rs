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

//! Utility to test the conformance tests from other implementation of Starlark
extern crate codemap;
extern crate codemap_diagnostic;
extern crate starlark;

use std::fs::File;
use std::io::prelude::*;
use std::io::{self, Write};
use std::path::Path;
use std::sync::{Arc, Mutex};
use testutil::codemap::CodeMap;
use testutil::codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use testutil::starlark::eval::simple::eval;
use testutil::starlark::stdlib::global_environment;

/// Load a file and convert it to a vector of string (separated by ---) to be evaluated separately.
fn read_input(path: &str) -> Vec<(usize, String)> {
    let mut content = String::new();
    let mut file = File::open(path).unwrap();
    file.read_to_string(&mut content).unwrap();
    let mut v: Vec<(usize, String)> = content
        .split("\n---\n")
        .map(|x| (0, x.to_owned()))
        .collect();
    let mut idx = 1;
    for mut el in &mut v {
        el.0 = idx;
        idx += el.1.chars().filter(|x| *x == '\n').count() + 2 // 2 = separator new lines
    }
    v
}

fn assert_diagnostic(
    d: Diagnostic,
    expected: &str,
    path: &str,
    offset: usize,
    map: &Arc<Mutex<CodeMap>>,
) -> bool {
    let expected = expected.to_lowercase();
    let msg = if d.spans.is_empty() || d.spans[0].label.is_none() {
        d.message.clone()
    } else {
        let label = d.spans[0].label.clone();
        format!("{} ({})", d.message, label.unwrap())
    };
    if !msg.to_lowercase().contains(&expected) {
        io::stderr()
            .write(
                &format!(
                    "Expected error '{}' at {}:{}, got {}\n",
                    expected, path, offset, msg,
                )
                .into_bytes(),
            )
            .unwrap();
        Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[d]);
        false
    } else {
        true
    }
}

fn run_conformance_test(path: &str) -> bool {
    let map = Arc::new(Mutex::new(CodeMap::new()));
    let global = global_environment();
    global.freeze();
    let mut prelude = global.child("PRELUDE");
    eval(
        &map,
        "PRELUDE",
        r#"
def assert_eq(x, y):
  if x != y:
    fail("%r != %r" % (x, y))

def assert_(cond, msg="assertion failed"):
  if not cond:
    fail(msg)
"#,
        starlark::syntax::dialect::Dialect::Bzl,
        &mut prelude,
    )
    .unwrap();
    prelude.freeze();
    for (offset, content) in read_input(path) {
        let err = if let Some(x) = content.find("###") {
            let err = content.get(x + 3..).unwrap().trim();
            err.get(..err.find("\n").unwrap_or(err.len())).unwrap()
        } else {
            ""
        };
        match eval(
            &map,
            &format!("{}<{}>", path, offset),
            &content,
            starlark::syntax::dialect::Dialect::Bzl,
            &mut prelude.child(&path),
        ) {
            Err(p) => {
                if err.is_empty() {
                    Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
                    return false;
                } else if !assert_diagnostic(p, err, path, offset, &map) {
                    return false;
                }
            }
            _ => {
                if !err.is_empty() {
                    io::stderr()
                        .write(
                            &format!(
                                "Expected error '{}' at {}:{}, got success",
                                err, path, offset,
                            )
                            .into_bytes(),
                        )
                        .unwrap();
                    return false;
                }
            }
        }
    }
    return true;
}

pub fn do_conformance_test(path: &str) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
    let path = path.to_str().unwrap();
    assert!(run_conformance_test(path));
}
