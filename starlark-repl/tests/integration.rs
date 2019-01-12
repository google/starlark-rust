extern crate assert_cmd;

use assert_cmd::prelude::*;
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

fn make_file(content: &str) -> tempfile::NamedTempFile {
    let mut file = tempfile::NamedTempFile::new().unwrap();
    writeln!(file, "{}", content).unwrap();
    file
}
