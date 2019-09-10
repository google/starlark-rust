# Starlark in Rust - REPL
_A REPL for the Starlark language in Rust_

**Disclaimer:** This is not an officially supported Google product. This project is supported
on a best-effort basis and [welcome contributions](CONTRIBUTING.md).

[Starlark](https://github.com/bazelbuild/starlark), formerly codenamed Skylark, is a non-Turing
complete language based on Python that was made for the [Bazel build system](https://bazel.build) to
define compilation plugin.

This REPL uses [starlark](https://crates.io/crates/starlark) crates.

## Usage

A command line interpreter is provided by this project, it can interpret files
passed at the command line and also start a REPL (Read-Eval-Print Loop).
The usage of this program is:

```
Starlark in Rust interpreter

USAGE:
    starlark-rust [FLAGS] [OPTIONS] [file]...

FLAGS:
    -a, --ast           Parse and print AST instead of evaluating.
    -b, --build-file    Parse the build file format instead of full Starlark. See https://docs.rs/starlark/0.3.0-
                        pre/starlark/eval/index.html#build_file
    -h, --help          Prints help information
    -r, --repl          Run a REPL after files have been parsed.
    -V, --version       Prints version information

OPTIONS:
    -c <command>        Starlark command to run after files have been parsed.

ARGS:
    <file>...    Files to interpret
```
