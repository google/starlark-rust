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
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::{env, process};

fn main() {
    let nightly = query_rust_version_is_nightly();

    test_cases("tests/java-testcases", &TestOrBench::Test);
    test_cases("tests/rust-testcases", &TestOrBench::Test);
    test_cases("tests/go-testcases", &TestOrBench::Test);
    if nightly {
        println!("cargo:rustc-cfg=rustc_nightly");
        // Benches only work in nightly
        test_cases("benches/rust-benches", &TestOrBench::Bench);
    }
}

fn version_is_nightly(version: &str) -> bool {
    version.contains("nightly")
}

fn query_rust_version_is_nightly() -> bool {
    let rustc = env::var("RUSTC").expect("RUSTC unset");

    let mut child = process::Command::new(rustc)
        .args(&["--version"])
        .stdin(process::Stdio::null())
        .stdout(process::Stdio::piped())
        .spawn()
        .expect("spawn rustc");

    let mut rustc_version = String::new();

    child
        .stdout
        .as_mut()
        .expect("stdout")
        .read_to_string(&mut rustc_version)
        .expect("read_to_string");
    assert!(child.wait().expect("wait").success());

    version_is_nightly(&rustc_version)
}

enum TestOrBench {
    Test,
    Bench,
}

fn format_test_content(path: &Path, test_or_bench: &TestOrBench) -> String {
    let test_name = path.file_stem().unwrap().to_str().unwrap();
    match test_or_bench {
        TestOrBench::Test => format!(
            r#"
#[test]
fn test_{}() {{
    do_conformance_test("{}")
}}
"#,
            test_name,
            path.to_str().unwrap(),
        ),
        TestOrBench::Bench => format!(
            r#"
#[bench]
fn bench_{}(bencher: &mut Bencher) {{
    do_bench(bencher, "{}")
}}
"#,
            test_name,
            path.to_str().unwrap(),
        ),
    }
}

fn test_cases(path: &str, test_or_bench: &TestOrBench) {
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
        if path_entry.extension().unwrap().to_str().unwrap() != "md" {
            // Exclude markdown files
            let content =
                format_test_content(path_entry.strip_prefix(base).unwrap(), test_or_bench);
            outfile.write(content.as_bytes()).unwrap();
        }
    }
}
