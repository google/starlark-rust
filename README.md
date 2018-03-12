# Starlark in Rust
_An implementation in Rust of the Starlark language_

Starlark, formerly codenamed Skylark, is a non-Turing complete language based
on Python that was made for the [Bazel build system](https://bazel.build) to
define compilation plugin.

Starlark has at least 3 implementations: a [Java one for Bazel](
https://github.com/bazelbuild/bazel/tree/master/src/main/java/com/google/devtools/skylark),
a [go one](https://github.com/google/skylark) and this one.

This interpreter was made using the [specification from the go version](
https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
and the Python 3 documentation when things were unclear.

This interpreter does not support most of the go extensions (e.g. bitwise
operator or floating point). It does not include the `set()` type either (the
Java implementation use a custom type, `depset`, instead). It uses signed 64-bit
integer.

## Usage

You can depend on this crate `starlark`, it is documented using [rustdoc](TODO).

A command line interpreter is also provided by this project, it can interpret
files passed at the command line and also start a REPL (Read-Eval-Print Loop).
The usage of this program is:

```sh
$ starlark --help
[Starlark in Rust interpretor]

Usage: ./target/release/starlark [options] [file1..filen]


Options:
    -b, --build_file    Parse the build file format instead of full Starlark.
    -h, --help          Show the usage of this program.
    -r, --repl          Run a REPL after files have been parsed.
```

## Development

### Build

This project build with [Cargo](https://doc.rust-lang.org/stable/cargo/). Simply
run `cargo test` to test it, `cargo build --release` to build a release version
and `cargo run` to run the command-line interpreter.

### List of feature needed to be implemented before releasing

- Add conformance tests from other implementations.

### Possible improvements and optimizations

* Errors:
  - When an identifier is not found, we can suggest close identifier / keyword.
  - Fix suggestions maybe?
  - Better error spans.
  - Recoverable errors (don't stop at the first error, continue parsing).
* Evaluation:
  - Static rewrite of the AST before evaluation (e.g. for constant values)
  - Rewrite of `+=` so that we do not recompute `index()` in `a[index()] += 1`
    (right now `+=` is equivalent to `a[index()] = a[index()] + 1`).
* Awesome feature:
  - Implement a debugging protocol
