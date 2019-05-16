// Copyright 2019 The Starlark in Rust Authors
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

use codemap::CodeMap;
use codemap_diagnostic::{ColorConfig, Emitter};
use linked_hash_map::LinkedHashMap;
use starlark::eval::simple::eval;
use starlark::stdlib::global_environment_with_extensions;
use starlark::syntax::dialect::Dialect;
use starlark::values::error::ValueError;
use std::fs::File;
use std::io::Read;
use std::sync::{Arc, Mutex};
use test::Bencher;

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
    )
    .unwrap();
    prelude.freeze();

    let mut env = prelude.child("run");
    match eval(&map, path, &content, Dialect::Bzl, &mut env) {
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
        match bench_func.call(&[], env, Vec::new(), LinkedHashMap::new(), None, None) {
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
