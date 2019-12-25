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

use crate::environment::Environment;
use crate::environment::EnvironmentError;
use crate::environment::TypeValues;
use crate::eval::call_stack::CallStack;
use crate::eval::locals::Locals;
use crate::eval::FileLoader;
use crate::values::Value;
use codemap::CodeMap;
use std::sync::Arc;
use std::sync::Mutex;

/// A structure holding all the data about the evaluation context
/// (scope, load statement resolver, ...)
pub(crate) struct EvaluationContext<'a, E: EvaluationContextEnvironment> {
    // Locals and captured context.
    pub(crate) env: E,
    // Globals used to resolve type values, provided by the caller.
    pub(crate) type_values: &'a TypeValues,
    pub(crate) call_stack: &'a mut CallStack,
    pub(crate) map: Arc<Mutex<CodeMap>>,
}

/// Module-level or function environments are quite different,
/// this trait describes the differences.
pub(crate) trait EvaluationContextEnvironment {
    /// Get the (global) environment
    fn env(&self) -> &Environment;

    /// Get global variable by name
    fn get_global(&self, name: &str) -> Result<Value, EnvironmentError>;

    /// Panic if this environment is local
    fn assert_module_env(&self) -> &EvaluationContextEnvironmentModule;

    /// Set local variable
    fn set_local(&mut self, slot: usize, name: &str, value: Value);

    /// Get local variable
    fn get_local(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError>;
}

pub(crate) struct EvaluationContextEnvironmentModule<'a> {
    pub env: Environment,
    pub loader: &'a dyn FileLoader,
}

pub(crate) struct EvaluationContextEnvironmentLocal<'a> {
    pub globals: Environment,
    pub locals: IndexedLocals<'a>,
}

impl<'a> EvaluationContextEnvironment for EvaluationContextEnvironmentModule<'a> {
    fn env(&self) -> &Environment {
        &self.env
    }

    fn get_global(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.env.get(name)
    }

    fn assert_module_env(&self) -> &EvaluationContextEnvironmentModule {
        self
    }

    fn set_local(&mut self, _slot: usize, _name: &str, _value: Value) {
        unreachable!("not a local env")
    }

    fn get_local(&mut self, _slot: usize, _name: &str) -> Result<Value, EnvironmentError> {
        unreachable!("not a local env")
    }
}

impl<'a> EvaluationContextEnvironment for EvaluationContextEnvironmentLocal<'a> {
    fn env(&self) -> &Environment {
        &self.globals
    }

    fn get_global(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.globals.get(name)
    }

    fn assert_module_env(&self) -> &EvaluationContextEnvironmentModule {
        unreachable!("not a module env")
    }

    fn set_local(&mut self, slot: usize, name: &str, value: Value) {
        self.locals.set_slot(slot, name, value)
    }

    fn get_local(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        self.locals.get_slot(slot, name)
    }
}

/// Starlark `def` or comprehension local variables
pub(crate) struct IndexedLocals<'a> {
    // This field is not used at runtime, but could be used for debugging or
    // for better diagnostics in the future
    pub local_defs: &'a Locals,
    /// Local variables are stored in this array. Names to slots are  mapped
    /// during analysis phase. Note access by index is much faster than by name.
    locals: Box<[Option<Value>]>,
}

impl<'a> IndexedLocals<'a> {
    pub fn new(local_defs: &'a Locals) -> IndexedLocals<'a> {
        IndexedLocals {
            local_defs,
            locals: vec![None; local_defs.len()].into_boxed_slice(),
        }
    }

    pub fn get_slot(&self, slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        match self.locals[slot].clone() {
            Some(value) => Ok(value),
            None => Err(EnvironmentError::LocalVariableReferencedBeforeAssignment(
                name.to_owned(),
            )),
        }
    }

    pub fn set_slot(&mut self, slot: usize, _name: &str, value: Value) {
        self.locals[slot] = Some(value);
    }
}
