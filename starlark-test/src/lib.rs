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
use starlark::stdlib::global_environment_with_extensions;
use starlark::syntax::dialect::Dialect;
use starlark::values::error::ValueError;
use std::fs::File;
use std::io::prelude::*;
use std::io::{self, Write};
use std::sync::{Arc, Mutex};
#[cfg(rustc_nightly)]
use test::Bencher;

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

pub fn do_conformance_test(path: &str, content: &str) {
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

    let errors: Vec<_> = content
        .lines()
        .enumerate()
        .filter_map(|(i, line)| {
            if let Some(x) = line.find("###") {
                Some((i + 1, line.get(x + 3..).unwrap().trim()))
            } else {
                None
            }
        })
        .collect();

    assert!(errors.len() <= 1, "test may contain at most one error");

    let err = if errors.is_empty() {
        None
    } else {
        Some(errors[0])
    };

    match eval(
        &map,
        path,
        &content,
        starlark::syntax::dialect::Dialect::Bzl,
        &mut prelude.child(path),
        global.clone(),
    ) {
        Err(p) => match err {
            Some((offset, err)) => {
                if !assert_diagnostic(p, err, "test", offset, &map) {
                    panic!();
                }
            }
            None => {
                Emitter::stderr(ColorConfig::Always, Some(&map.lock().unwrap())).emit(&[p]);
                panic!();
            }
        },
        _ => {
            if let Some((offset, err)) = err {
                io::stderr()
                    .write_all(
                        &format!(
                            "Expected error '{}' at {}:{}, got success",
                            err, path, offset
                        )
                        .into_bytes(),
                    )
                    .unwrap();
                panic!();
            }
        }
    }
}

#[cfg(not(rustc_nightly))]
pub struct Bencher {}

#[cfg(not(rustc_nightly))]
impl Bencher {
    pub fn iter<T, F>(&mut self, mut _inner: F)
    where
        F: FnMut() -> T,
    {
        // Bencher included here to typecheck `do_bench` function
        // in stable and also to mute unused imports warnings
        panic!("Bencher available only in nightly");
    }
}

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
