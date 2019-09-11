# Starlark in Rust
_An implementation in Rust of the Starlark language_

[![Build
Status](https://travis-ci.org/google/starlark-rust.svg?branch=master)](https://travis-ci.org/google/starlark-rust)

**Disclaimer:** This is not an officially supported Google product. This project is supported
on a best-effort basis and [welcome contributions](CONTRIBUTING.md).

[Starlark](https://github.com/bazelbuild/starlark), formerly codenamed Skylark, is a non-Turing
complete language based on Python that was made for the [Bazel build system](https://bazel.build) to
define compilation plugin.

Starlark has at least 3 implementations: a [Java one for Bazel](
https://github.com/bazelbuild/bazel/tree/master/src/main/java/com/google/devtools/skylark),
a [Go one](https://github.com/google/skylark) and this one.

This interpreter was made using the [specification from the go version](
https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
and the Python 3 documentation when things were unclear.

This interpreter does not support most of the go extensions (e.g. bitwise
operator or floating point). It optionally includes a `set` type
(by explicitly including `starlark::linked_hash_set::global()` environment),
as an extension which is not specified in [the
official Starlark specification](https://github.com/bazelbuild/starlark/blob/master/spec.md), but note that this
is just an insertion-order-preserving set, and does not have optimisations for nesting as can be found in the
starlark Java implemnetation's [depset](https://docs.bazel.build/versions/master/skylark/lib/depset.html) implementation.
It uses signed 64-bit integers.

## Usage

### Crate

You can depend on the `starlark` crate, it is documented using [docs.rs](https://docs.rs/crate/starlark).
Examples are listed under [starlark/examples](starlark/examples). You can run the examples
using `cargo run --example`, such as

```sh
echo "str([x * 2 for x in range(10)])" | cargo run --example starlark-simple-cli
```

### Command line REPL

A command line interpreter is also provided by this project under [starlark-repl](starlark-repl),
it can interpret files passed at the command line and also start a REPL (Read-Eval-Print Loop).
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

## Development

### Build

This project build with [Cargo](https://doc.rust-lang.org/stable/cargo/). Simply
run `cargo test` to test it, `cargo build --release` to build a release version
and `cargo run` to run the command-line interpreter.

### Possible improvements and optimizations

* Errors:
  - When an identifier is not found, we can suggest close identifier / keyword.
  - Fix suggestions maybe?
  - Better error spans.
  - Recoverable errors (don't stop at the first error, continue parsing).
* Evaluation:
  - Static rewrite of the AST before evaluation (e.g. for constant values)
* Awesome feature:
  - Implement a debugging protocol server side (compatible with the Java one,
    see (bazelbuild/vscode-bazel#6)).
