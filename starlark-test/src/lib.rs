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

//! Utility to test the tests and benches

#![cfg_attr(rustc_nightly, feature(test))]

#[cfg(rustc_nightly)]
extern crate test;

use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Diagnostic, Emitter};
use linked_hash_map::LinkedHashMap;
use starlark::environment::TypeValues;
use starlark::eval::call_stack::CallStack;
use starlark::eval::simple::eval;
use starlark::gc;
use starlark::stdlib::global_environment_with_extensions;
use starlark::syntax::dialect::Dialect;
use starlark::values::error::ValueError;
use std::fs::File;
use std::io::prelude::*;
use std::io::{self, Write};
use std::path::Path;
use std::sync::{Arc, Mutex};
#[cfg(rustc_nightly)]
use test::Bencher;

/// Load a file and convert it to a vector of string (separated by ---) to be evaluated separately.
fn read_input(path: &str) -> Vec<(usize, String)> {
    let mut content = String::new();
    let mut file = File::open(path).unwrap();
    file.read_to_string(&mut content).unwrap();
    let mut v: Vec<(usize, String)> = content
        .split("\n---\n")
        .map(|x| (0, x.to_owned()))
        .collect();
    let mut idx = 0;
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
        let error_code = d.code.clone().unwrap_or_else(|| "".to_owned());
        format!("[{}] {} ({})", error_code, d.message, label.unwrap())
    };
    if !msg.to_lowercase().contains(&expected) {
        io::stderr()
            .write_all(
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
    let global = global_environment_with_extensions();
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
        global.clone(),
    )
    .unwrap();
    prelude.freeze();
    for (offset, content) in read_input(path) {
        let err = if let Some(x) = content.find("###") {
            let err = content.get(x + 3..).unwrap().trim();
            err.get(..err.find('\n').unwrap_or_else(|| err.len()))
                .unwrap()
        } else {
            ""
        };
        let content = std::iter::repeat("\n").take(offset).collect::<String>() + &content;
        match eval(
            &map,
            &path,
            &content,
            starlark::syntax::dialect::Dialect::Bzl,
            &mut prelude.child(&path),
            global.clone(),
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
                        .write_all(
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
    true
}

pub fn do_conformance_test(path: &str) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
    let path = path.to_str().unwrap();
    assert!(run_conformance_test(path));
}

#[cfg(rustc_nightly)]
pub fn do_bench(bencher: &mut Bencher, path: &str) {
    let mut content = String::new();
    let mut file = File::open(path).unwrap();
    file.read_to_string(&mut content).unwrap();
    drop(file);

    let map = Arc::new(Mutex::new(CodeMap::new()));
    let global = global_environment_with_extensions();
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
        global.clone(),
    )
    .unwrap();
    prelude.freeze();

    let mut env = prelude.child("run");
    match eval(&map, path, &content, Dialect::Bzl, &mut env, global) {
        Ok(_) => (),
        Err(p) => {
            Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
            panic!();
        }
    }

    env.freeze();

    let bench_func = env.get("bench").expect("bench function is not found");

    let _heap_guard = gc::push_heap(env.heap());

    bencher.iter(|| {
        let env = env.child("bench");
        match bench_func.call(
            &CallStack::default(),
            TypeValues::new(env),
            Vec::new(),
            LinkedHashMap::new(),
            None,
            None,
        ) {
            Ok(r) => r,
            Err(ValueError::DiagnosedError(e)) => {
                Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[e]);
                panic!();
            }
            Err(e) => {
                panic!("{:?}", e);
            }
        }
    });
}
