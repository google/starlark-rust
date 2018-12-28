# Starlark in Rust
_An implementation in Rust of the Starlark language_

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
operator or floating point). It does not include the `set()` type either ([the
official Starlark specification](https://github.com/bazelbuild/starlark/blob/master/spec.md)
does not have them either). It uses signed 64-bit integers.
