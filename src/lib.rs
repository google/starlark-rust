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

//! A Starlark interpreter library in rust.
//!
//! Starlark, formerly codenamed Skylark, is a non-Turing complete language based on Python that
//! was made for the [Bazel build system](https://bazel.build) to define compilation plugin.
//!
//! Starlark has at least 3 implementations: a [Java one for Bazel](
//! https://github.com/bazelbuild/bazel/tree/master/src/main/java/com/google/devtools/skylark),
//! a [go one](https://github.com/google/skylark) and this one.
//!
//! This interpreter was made using the [specification from the go version](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
//! and the Python 3 documentation when things were unclear.
//!
//! This interpreter does not support most of the go extensions (e.g. bitwise operator or
//! floating point). It does not include the `set()` type either (the Java implementation use a
//! custom type, `depset`, instead). It uses signed 64-bit integer.
//!
//! # Usage
//!
//! The library can be used to define a dialect of Starlark (e.g. for a build system).
//!
//! The methods in the [eval](eval) modules can be used to evaluate Starlark code:
//!   * General purpose [eval](eval::eval) and [eval_file](eval::eval_file) function evaluate
//!     Starlark code and return the result of the last statement. Those are generic purpose
//!     function to be used when rewiring load statements.
//!   * A file loader that simply load relative path to the program is provided by the
//!     [eval::simple] module. This module also contains version of [eval](eval::simple::eval) and
//!     [eval_file](eval::simple::eval_file) that use this file loader.
//!   * Interactive versions of those function are provided in the [eval::interactive] module.
//!     Those function are printing the result / diagnostic to the stdout / stderr instead of
//!     returning an output.
//!   * Finally, a REPL loop can be invoked with the [eval::repl::repl] function.
//!
//! # Defining a Starlark dialect
//!
//! To specify a new Starlark dialect, the global [Environment](environment::Environment) can be
//! edited, adding functions or constants. The [skylark_modules!](skylark_modules) macro let you
//! define new function with limited boilerplate.
//!
//! Those added function or macros can however return their own type, all of them should implement
//! the [TypedValue](values::TypedValue) trait. See the documentation of the [values](values)
//! module.
//!
//! # Content of the default global environment
//!
//! The default global environment is returned by the
//! [stdlib::global_environment] function and add the `True`,
//! `False` and `None` constants, as well as the functions in the [stdlib] module.
//!
//! # Provided types
//!
//! The [values](values) module provide the following types:
//!
//! * integer (signed 64bit), bool, and NoneType,
//! * [string](values::string),
//! * [dictionary](values::dict),
//! * [list](values::list),
//! * [tuple](values::tuple), and
//! * [function](values::function).
pub mod environment;
#[doc(hidden)]
pub mod syntax;
pub mod values;
#[macro_use]
pub mod eval;
#[macro_use]
pub mod stdlib;
extern crate codemap;
extern crate codemap_diagnostic;
extern crate linefeed;
extern crate linked_hash_map;
