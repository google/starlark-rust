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
use crate::eval::expr::GlobalOrSlot;
use crate::eval::globals::Globals;
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
    fn get_global(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError>;

    /// Panic if this environment is local
    fn assert_module_env(&self) -> &EvaluationContextEnvironmentModule;

    /// Set local variable
    fn set_local(&mut self, slot: usize, name: &str, value: Value);

    /// Get local variable
    fn get_local(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError>;

    fn get(&mut self, name_slot: &GlobalOrSlot) -> Result<Value, EnvironmentError> {
        let GlobalOrSlot { name, local, slot } = name_slot;
        match local {
            true => self.get_local(*slot, name),
            false => self.get_global(*slot, name),
        }
    }

    fn set_global(&mut self, slot: usize, name: &str, value: Value)
        -> Result<(), EnvironmentError>;

    fn set(&mut self, name_slot: &GlobalOrSlot, value: Value) -> Result<(), EnvironmentError> {
        let GlobalOrSlot { name, local, slot } = name_slot;
        match local {
            true => Ok(self.set_local(*slot, name, value)),
            false => self.set_global(*slot, name, value),
        }
    }

    fn top_level_local_to_slot(&self, name: &str) -> usize;
}

pub(crate) struct EvaluationContextEnvironmentModule<'a> {
    pub env: Environment,
    pub globals: IndexedGlobals<'a>,
    pub loader: &'a dyn FileLoader,
}

pub(crate) struct EvaluationContextEnvironmentLocal<'a> {
    pub globals: IndexedGlobals<'a>,
    pub locals: IndexedLocals<'a>,
}

impl<'a> EvaluationContextEnvironment for EvaluationContextEnvironmentModule<'a> {
    fn env(&self) -> &Environment {
        &self.env
    }

    fn get_global(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        self.globals.get_slot(slot, name)
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

    fn set_global(
        &mut self,
        slot: usize,
        name: &str,
        value: Value,
    ) -> Result<(), EnvironmentError> {
        self.globals.set_slot(slot, name, value)
    }

    fn top_level_local_to_slot(&self, _name: &str) -> usize {
        unreachable!("not a local env")
    }
}

impl<'a> EvaluationContextEnvironment for EvaluationContextEnvironmentLocal<'a> {
    fn env(&self) -> &Environment {
        &self.globals.env
    }

    fn get_global(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        self.globals.get_slot(slot, name)
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

    fn set_global(
        &mut self,
        _slot: usize,
        _name: &str,
        _value: Value,
    ) -> Result<(), EnvironmentError> {
        unreachable!("assign to global in local environment")
    }

    fn top_level_local_to_slot(&self, name: &str) -> usize {
        self.locals.local_defs.top_level_name_to_slot(name).unwrap()
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

pub(crate) struct IndexedGlobals<'a> {
    // This field is not used at runtime, but could be used for debugging or
    // for better diagnostics in the future.
    _global_defs: &'a Globals,
    /// Global variables are cached in this array. Names to slots are  mapped
    /// during analysis phase. Note access by index is much faster than by name.
    globals: Box<[Option<Value>]>,
    /// Actual storage of variables.
    env: Environment,
}

impl<'a> IndexedGlobals<'a> {
    pub fn new(global_defs: &'a Globals, env: Environment) -> IndexedGlobals<'a> {
        IndexedGlobals {
            _global_defs: global_defs,
            globals: vec![None; global_defs.len()].into_boxed_slice(),
            env,
        }
    }

    fn get_slot(&mut self, slot: usize, name: &str) -> Result<Value, EnvironmentError> {
        match &mut self.globals[slot] {
            Some(value) => Ok(value.clone()),
            o @ None => {
                let value = self.env.get(name)?;
                *o = Some(value.clone());
                Ok(value)
            }
        }
    }

    fn set_slot(&mut self, slot: usize, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.env.set(name, value.clone())?;
        self.globals[slot] = Some(value);
        Ok(())
    }
}
