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

use codemap::CodeMap;
use starlark::eval::simple::eval;
use starlark::stdlib::global_environment;
use starlark::syntax::dialect::Dialect;
use starlark::values::function::Function;
use starlark::values::Value;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

/// An example of how to call Starlark from Rust program.
#[test]
fn call_starlark_from_rust() {
    let program = "def inc(x): return x + 1";
    let map = Arc::new(Mutex::new(CodeMap::new()));
    let global = global_environment();
    global.freeze();
    let mut env = global.child("my");
    eval(&map, "inline.bzl", program, Dialect::Bzl, &mut env).unwrap();
    let inc = env.get("inc").unwrap();
    let result = inc
        .call(
            &[],
            env.child("call"),
            vec![Value::new(17)],
            HashMap::new(),
            None,
            None,
        )
        .unwrap();
    assert_eq!(18, result.to_int().unwrap());
}

/// An example how to inject a Rust function into a Starlark program.
#[test]
fn call_rust_from_starlark() {
    let program = "build_house();\
                   plant_tree('oak');\
                   plant_tree('birch');\
                   ";
    let map = Arc::new(Mutex::new(CodeMap::new()));
    let global = global_environment();

    #[derive(Default)]
    struct Ground {
        houses: u32,
        trees: Vec<String>,
    }

    let ground = Rc::new(RefCell::new(Ground::default()));
    let ground1 = ground.clone();
    let ground2 = ground.clone();

    global
        .set(
            "plant_tree",
            Function::new_native_1("plant_tree".to_owned(), move |name| {
                (*ground1).borrow_mut().trees.push(name);
                Ok(())
            }),
        )
        .unwrap();
    global
        .set(
            "build_house",
            Function::new_native_0("build_house".to_owned(), move || {
                (*ground2).borrow_mut().houses += 1;
                Ok(())
            }),
        )
        .unwrap();
    global.freeze();
    let mut env = global.child("my");
    eval(&map, "inline.bzl", program, Dialect::Bzl, &mut env).unwrap();

    assert_eq!(
        vec!["oak".to_owned(), "birch".to_owned()],
        (*ground).borrow_mut().trees
    );
    assert_eq!(1, (*ground).borrow_mut().houses);
}
