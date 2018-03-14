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

macro_rules! assert_diagnostics {
    ($e: expr, $m: expr) => (
        if !$e.is_empty() {
            let nb_errors = $e.len();
            let locked = $m.lock();
            let codemap = locked.unwrap();
            let mut emitter = codemap_diagnostic::Emitter::stderr(
                codemap_diagnostic::ColorConfig::Always, Some(&codemap));
            emitter.emit(&$e);
            panic!("There was {} parse errors", nb_errors);
        }
    )
}
