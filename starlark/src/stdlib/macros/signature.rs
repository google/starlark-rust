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

#![doc(hidden)]

//! Signature construction utilities used in macros.

use crate::values::function::FunctionParameter;
use crate::values::Value;
use std::mem;

/// Signature builder utility used in macros. Do not use directly.
#[derive(Default)]
pub struct SignatureBuilder {
    params: Vec<FunctionParameter>,
    seen_slash: bool,
}

impl SignatureBuilder {
    pub fn push_normal(&mut self, name: &str) {
        self.params.push(FunctionParameter::Normal(name.to_owned()));
    }

    pub fn push_optional(&mut self, name: &str) {
        self.params
            .push(FunctionParameter::Optional(name.to_owned()));
    }

    pub fn push_with_default_value<V: Into<Value>>(&mut self, name: &str, default_value: V) {
        self.params.push(FunctionParameter::WithDefaultValue(
            name.to_owned(),
            default_value.into(),
        ));
    }

    pub fn push_kwargs(&mut self, name: &str) {
        self.params
            .push(FunctionParameter::KWArgsDict(name.to_owned()));
    }

    pub fn push_args(&mut self, name: &str) {
        self.params
            .push(FunctionParameter::ArgsArray(name.to_owned()));
    }
    pub fn push_slash(&mut self) {
        assert!(!self.seen_slash);
        self.seen_slash = true;
        self.params = mem::replace(&mut self.params, Vec::new())
            .into_iter()
            .map(|p| match p {
                FunctionParameter::Normal(n) => FunctionParameter::Normal(format!("${}", n)),
                FunctionParameter::Optional(n) => FunctionParameter::Optional(format!("${}", n)),
                FunctionParameter::WithDefaultValue(n, value) => {
                    FunctionParameter::WithDefaultValue(format!("${}", n), value)
                }
                FunctionParameter::ArgsArray(..) => panic!("/ after *args"),
                FunctionParameter::KWArgsDict(..) => panic!("/ after **args"),
            })
            .collect();
    }

    pub fn build(self) -> Vec<FunctionParameter> {
        self.params
    }
}
