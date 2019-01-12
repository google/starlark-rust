extern crate assert_cmd;
extern crate predicates;

use assert_cmd::prelude::*;
use predicates::str::contains;
use std::io::Write;
use std::process::Command;

#[test]
fn outputs_last_command_value() {
    Command::main_binary()
        .unwrap()
        .arg("-c")
        .arg("5\n1 + 1")
        .assert()
        .success()
        .stdout("2\n");
}

#[test]
fn outputs_last_file_values() {
    let f1 = make_file("0");
    let f2 = make_file("");
    let f3 = make_file("None");
    let f4 = make_file("2\n3\n\"Hello\"");

    Command::main_binary()
        .unwrap()
        .arg(f1.path())
        .arg(f2.path())
        .arg(f3.path())
        .arg(f4.path())
        .assert()
        .success()
        .stdout("0\n\"Hello\"\n");
}

#[test]
fn error_in_command() {
    Command::main_binary()
        .unwrap()
        .arg("-c")
        .arg("x")
        .assert()
        .code(2)
        .stderr(contains("Variable 'x' not found"));
}

#[test]
fn error_in_file() {
    let f = make_file("x");

    Command::main_binary()
        .unwrap()
        .arg(f.path())
        .assert()
        .code(2)
        .stderr(contains("Variable 'x' not found"));
}

#[test]
fn files_environments_are_isolated() {
    let f1 = make_file("x = 1");
    let f2 = make_file("x");

    Command::main_binary()
        .unwrap()
        .arg(f1.path())
        .arg(f2.path())
        .assert()
        .code(2)
        .stderr(contains("Variable 'x' not found"));
}

fn make_file(content: &str) -> tempfile::NamedTempFile {
    let mut file = tempfile::NamedTempFile::new().unwrap();
    writeln!(file, "{}", content).unwrap();
    file
}
