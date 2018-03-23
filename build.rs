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
use std::env;
use std::fs::File;
use std::path::Path;
use std::fs;
use std::io::prelude::*;
extern crate lalrpop;

fn main() {
    conformance_test_cases("tests/testcases");
    conformance_test_cases("tests/go-testcases");
    lalrpop();
}

fn lalrpop() {
    // A test
    println!("cargo:rerun-if-changed=src/syntax/grammar.lalrpop");
    lalrpop::Configuration::new()
        .use_cargo_dir_conventions()
        .always_use_colors()
        .emit_report(true)
        .process_file("src/syntax/grammar.lalrpop")
        .unwrap();
}

fn conformance_test_cases(path: &str) {
    println!("cargo:rerun-if-changed={}", path);
    let outfile_path = Path::new(&env::var("OUT_DIR").unwrap()).join(format!("{}.rs", path));
    fs::create_dir_all(outfile_path.parent().unwrap()).unwrap();
    let mut outfile = File::create(outfile_path).unwrap();
    let cargo_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let base = Path::new(&cargo_dir);
    let d = base.join(path);
    let paths = fs::read_dir(d).unwrap();
    for p in paths {
        let path_entry = p.unwrap().path();
        let path = path_entry.strip_prefix(&base).unwrap().to_str().unwrap();
        if path_entry.extension().unwrap().to_str().unwrap() != "md" {
            // Exclude markdown files
            write!(
                outfile,
                r#"
#[test]
fn test_{}() {{
    do_conformance_test("{}")
}}
        "#,
                path_entry.file_stem().unwrap().to_str().unwrap(),
                path
            ).unwrap();
        }
    }
}
