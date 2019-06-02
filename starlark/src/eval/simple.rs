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

//! Define simpler version of the evaluation function
use super::Dialect;
use super::{EvalException, FileLoader};
use crate::environment::Environment;
use crate::values::*;
use codemap::CodeMap;
use codemap_diagnostic::Diagnostic;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

/// A simple FileLoader that load file from disk and cache the result in a hashmap.
#[derive(Clone)]
pub struct SimpleFileLoader {
    map: Arc<Mutex<HashMap<String, Environment>>>,
    parent_env: Environment,
    codemap: Arc<Mutex<CodeMap>>,
}

impl SimpleFileLoader {
    pub fn new(map: &Arc<Mutex<CodeMap>>, parent_env: Environment) -> SimpleFileLoader {
        SimpleFileLoader {
            map: Arc::new(Mutex::new(HashMap::new())),
            parent_env,
            codemap: map.clone(),
        }
    }
}

impl FileLoader for SimpleFileLoader {
    fn load(&self, path: &str) -> Result<Environment, EvalException> {
        {
            let lock = self.map.lock().unwrap();
            if lock.contains_key(path) {
                return Ok(lock.get(path).unwrap().clone());
            }
        } // Release the lock
        let mut env = self.parent_env.child(path);
        if let Err(d) = super::eval_file(
            &self.codemap,
            path,
            Dialect::Bzl,
            &mut env,
            self.parent_env.clone(),
            self.clone(),
        ) {
            return Err(EvalException::DiagnosedError(d));
        }
        env.freeze();
        self.map
            .lock()
            .unwrap()
            .insert(path.to_owned(), env.clone());
        Ok(env)
    }
}

/// Evaluate a string content, mutate the environment accordingly and return the evaluated value.
///
/// # Arguments
///
/// __This version uses the [`SimpleFileLoader`] implementation for
/// the file loader__
///
/// * map: the codemap object used for diagnostics
/// * path: the name of the file being evaluated, for diagnostics
/// * content: the content to evaluate
/// * dialect: Starlark language dialect
/// * env: the environment to mutate during the evaluation
pub fn eval(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    content: &str,
    dialect: Dialect,
    env: &mut Environment,
    file_loader_env: Environment,
) -> Result<Value, Diagnostic> {
    super::eval(
        map,
        path,
        content,
        dialect,
        env,
        file_loader_env.clone(),
        SimpleFileLoader::new(map, file_loader_env),
    )
}

/// Evaluate a file, mutate the environment accordingly and return the evaluated value.
///
/// __This version uses the [`SimpleFileLoader`] implementation for
/// the file loader__
///
/// # Arguments
///
/// * map: the codemap object used for diagnostics
/// * path: the file to parse and evaluate
/// * build: set to true if you want to evaluate a BUILD file or false to evaluate a .bzl file
/// * env: the environment to mutate during the evaluation
pub fn eval_file(
    map: &Arc<Mutex<CodeMap>>,
    path: &str,
    build: Dialect,
    env: &mut Environment,
    file_loader_env: Environment,
) -> Result<Value, Diagnostic> {
    super::eval_file(
        map,
        path,
        build,
        env,
        file_loader_env.clone(),
        SimpleFileLoader::new(map, file_loader_env),
    )
}
