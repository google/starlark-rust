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

use super::StarlarkParser;
use std::sync::{Arc, Mutex};
use syntax::ast::Statement;
use syntax::parser::parse_file;
use syntax::errors::SyntaxError;
use codemap;
use codemap_diagnostic;
use std::path::PathBuf;
use std::fs;

macro_rules! unwrap_parse {
    ($e: expr) => (
        {
            let lexer = super::lexer::Lexer::new($e);
            let mut codemap = codemap::CodeMap::new();
            let filespan = codemap.add_file("<test>".to_owned(), $e.to_string()).span;
            match StarlarkParser::new().parse($e, filespan, lexer) {
                Ok(x) => match x.node {
                    Statement::Statements(bv) => format!("{}", Statement::Statements(bv)),
                    y => panic!("Expected statements, got {:?}", y),
                }
                Err(e) => {
                    let codemap = Arc::new(Mutex::new(codemap));
                    let d = [e.to_diagnostic(filespan)];
                    assert_diagnostics!(d, codemap);
                    panic!("Got errors!");
                }
            }
        }
    )
}

#[test]
fn test_empty() {
    assert!(unwrap_parse!("\n").is_empty());
}

#[test]
fn test_top_level_comment() {
    assert!(unwrap_parse!("# Test").is_empty());
}

#[test]
fn test_top_level_load() {
    assert!(!unwrap_parse!(
        "\nload(\"//top/level/load.bzl\", \"top-level\")\n"
    ).is_empty());
    assert!(!unwrap_parse!(
        "\nload(\"//top/level/load.bzl\", \"top-level\")"
    ).is_empty());
    assert!(!unwrap_parse!(
        "\nload(\n  \"//top/level/load.bzl\",\n  \"top-level\",\n)\n"
    ).is_empty());
}

#[test]
fn test_top_level_assignation() {
    assert!(!unwrap_parse!("\n_ASSIGNATION = 'top-level'\n").is_empty());
}

#[test]
fn test_top_level_docstring() {
    assert!(!unwrap_parse!("\n\"\"\"Top-level docstring\"\"\"\n")
        .is_empty());
}

#[test]
fn test_top_level_def() {
    assert_eq!(
        unwrap_parse!("def toto():\n  pass\n"),
        "def toto():\n  pass\n"
    );
    // no new line at end of file
    assert_eq!(
        unwrap_parse!("def toto():\n  pass"),
        "def toto():\n  pass\n"
    );
    assert_eq!(
        unwrap_parse!("def toto():\n  pass\ndef titi(): return 1"),
        "def toto():\n  pass\ndef titi():\n  return 1\n"
    );
    assert_eq!(
        unwrap_parse!("def toto():\n  pass\n\ndef titi(): return 1"),
        "def toto():\n  pass\ndef titi():\n  return 1\n"
    );
    assert_eq!(unwrap_parse!("def t():\n\n  pass"), "def t():\n  pass\n");
}

#[test]
fn test_top_level_def_with_docstring() {
    assert_eq!(
        unwrap_parse!(
            "\"\"\"Top-level docstring\"\"\"

def toto():
  pass
"
        ),
        "\"Top-level docstring\"\ndef toto():\n  pass\n"
    );
}

#[test]
fn test_ifelse() {
    assert_eq!(
        unwrap_parse!("def d():\n  if True:\n    a\n  else:\n    b"),
        "def d():\n  if True:\n    a\n  else:\n    b\n"
    );
}

#[test]
fn test_kwargs_passing() {
    assert_eq!(
        unwrap_parse!("f(x, *a, **b); f(x, *a, **{a:b}); f(x, *[a], **b)"),
        "f(x, *a, **b)\nf(x, *a, **{a: b})\nf(x, *[a], **b)\n"
    );
}

#[test]
fn test_unary_op() {
    assert_eq!(unwrap_parse!("a = -1"), "a = -1\n");
    assert_eq!(unwrap_parse!("a = +1"), "a = +1\n");
    assert_eq!(unwrap_parse!("a = -a"), "a = -a\n");
    assert_eq!(unwrap_parse!("a = +a"), "a = +a\n");
}

#[test]
fn test_tuples() {
    assert_eq!(unwrap_parse!("a = (-1)"), "a = -1\n"); // Not a tuple
    assert_eq!(unwrap_parse!("a = (+1,)"), "a = (+1,)\n"); // But this is one
    assert_eq!(unwrap_parse!("a = ()"), "a = ()\n");
}

#[test]
fn test_return() {
    assert_eq!(
        unwrap_parse!("def fn(): return 1"),
        "def fn():\n  return 1\n"
    );
    assert_eq!(
        unwrap_parse!("def fn(): return a()"),
        "def fn():\n  return a()\n"
    );
    assert_eq!(unwrap_parse!("def fn(): return"), "def fn():\n  return\n");
}

#[test]
fn test_fncall_span() {
    let content = r#"def fn(a):
  fail(a)

fn(1)

fail(2)
"#;
    let lexer = super::lexer::Lexer::new(content);
    let mut codemap = codemap::CodeMap::new();
    let filespan = codemap
        .add_file("<test>".to_owned(), content.to_string())
        .span;
    match StarlarkParser::new().parse(content, filespan, lexer) {
        Ok(x) => {
            match x.node {
                Statement::Statements(bv) => {
                    let lines: Vec<usize> = bv.iter()
                        .map(|x| codemap.look_up_pos(x.span.low()).position.line)
                        .collect();
                    assert_eq!(lines, vec![0, 3, 5])
                }
                y => panic!("Expected statements, got {:?}", y),
            }
        }
        Err(e) => {
            let codemap = Arc::new(Mutex::new(codemap));
            let d = [e.to_diagnostic(filespan)];
            assert_diagnostics!(d, codemap);
            panic!("Got errors!");
        }
    }
}

#[test]
fn smoke_test() {
    let map = Arc::new(Mutex::new(codemap::CodeMap::new()));
    let mut diagnostics = Vec::new();
    let mut d = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    d.push("src/syntax/testcases");
    let paths = fs::read_dir(d.as_path()).unwrap();
    for p in paths {
        let path_entry = p.unwrap().path();
        let path = path_entry.to_str().unwrap();
        if path.ends_with(".bzl") {
            if let Result::Err(err) = parse_file(&map, path, false) {
                diagnostics.push(err);
            }
        }
    }
    assert_diagnostics!(diagnostics, map);
}
