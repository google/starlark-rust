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

//! The enviroment, called "Module" in [this spec](
//! https://github.com/google/skylark/blob/a0e5de7e63b47e716cca7226662a4c95d47bf873/doc/spec.md)
//! is the list of variable in the current scope. It can be frozen, after which all values from
//! this environment become immutable.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;
use crate::values::*;

// TODO: move that code in some common error code list?
// CM prefix = Critical Module
const FROZEN_ENV_ERROR_CODE: &str = "CM00";
const NOT_FOUND_ERROR_CODE: &str = "CM01";
const CANNOT_IMPORT_ERROR_CODE: &str = "CE02";

#[derive(Debug)]
#[doc(hidden)]
pub enum EnvironmentError {
    /// Raised when trying to change a variable on a frozen environment.
    TryingToMutateFrozenEnvironment,
    /// Variables was no found.
    VariableNotFound(String),
    /// Cannot import private symbol, i.e. underscore prefixed
    CannotImportPrivateSymbol(String),
}

impl Into<RuntimeError> for EnvironmentError {
    fn into(self) -> RuntimeError {
        RuntimeError {
            code: match self {
                EnvironmentError::TryingToMutateFrozenEnvironment => FROZEN_ENV_ERROR_CODE,
                EnvironmentError::VariableNotFound(..) => NOT_FOUND_ERROR_CODE,
                EnvironmentError::CannotImportPrivateSymbol(..) => CANNOT_IMPORT_ERROR_CODE,
            },
            label: match self {
                EnvironmentError::TryingToMutateFrozenEnvironment => {
                    "This value belong to a frozen environment".to_owned()
                }
                EnvironmentError::VariableNotFound(..) => "Variable was not found".to_owned(),
                EnvironmentError::CannotImportPrivateSymbol(ref s) => {
                    format!("Symbol '{}' is private", s)
                }
            },
            message: match self {
                EnvironmentError::TryingToMutateFrozenEnvironment => {
                    "Cannot mutate a frozen environment".to_owned()
                }
                EnvironmentError::VariableNotFound(s) => format!("Variable '{}' not found", s),
                EnvironmentError::CannotImportPrivateSymbol(s) => {
                    format!("Cannot import private symbol '{}'", s)
                }
            },
        }
    }
}

impl Into<ValueError> for EnvironmentError {
    fn into(self) -> ValueError {
        ValueError::Runtime(self.into())
    }
}

#[derive(Clone, Debug)]
pub struct Environment {
    env: Arc<RefCell<EnvironmentContent>>,
}

#[derive(Debug)]
struct EnvironmentContent {
    /// A name for this environment, used mainly for debugging.
    name_: String,
    /// Wether the environment is frozen or not.
    frozen: bool,
    /// Super environment that represent a higher scope than the current one
    parent: Option<Environment>,
    /// List of variable bindings
    ///
    /// These bindings include methods for native types, e.g. `string.isalnum`.
    variables: HashMap<String, Value>,
    /// List of static values of an object per type
    type_objs: HashMap<String, HashMap<String, Value>>,
}

impl Environment {
    /// Create a new environment
    pub fn new(name: &str) -> Environment {
        Environment {
            env: Arc::new(RefCell::new(EnvironmentContent {
                name_: name.to_owned(),
                frozen: false,
                parent: None,
                variables: HashMap::new(),
                type_objs: HashMap::new(),
            })),
        }
    }

    /// Get the object of type `obj_type`, and create it if none exists
    /// Get the object of type `obj_type`, and create it if none exists
    pub fn add_type_value(&self, obj: &str, attr: &str, value: Value) {
        self.env.borrow_mut().add_type_value(obj, attr, value)
    }

    /// Get a type value if it exists (e.g. list.index).
    pub fn get_type_value(&self, obj: &Value, id: &str) -> Option<Value> {
        self.env.borrow().get_type_value(obj, id)
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<String> {
        self.env.borrow().list_type_value(obj)
    }

    /// Create a new child environment for this environment
    pub fn child(&self, name: &str) -> Environment {
        Environment {
            env: Arc::new(RefCell::new(EnvironmentContent {
                name_: name.to_owned(),
                frozen: false,
                parent: Some(self.clone()),
                variables: HashMap::new(),
                type_objs: HashMap::new(),
            })),
        }
    }

    /// Create a new child environment
    /// Freeze the environment, all its value will become immutable after that
    pub fn freeze(&self) -> &Self {
        self.env.borrow_mut().freeze();
        self
    }

    /// Return the name of this module
    pub fn name(&self) -> String {
        self.env.borrow().name_.clone()
    }

    /// Set the value of a variable in that environment.
    pub fn set(&self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.env.borrow_mut().set(name, value)
    }

    /// Get the value of the variable `name`
    pub fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.env.borrow().get(name)
    }

    pub fn import_symbol(
        &mut self,
        env: &Environment,
        symbol: &str,
        new_name: &str,
    ) -> Result<(), EnvironmentError> {
        let first = symbol.chars().next();
        match first {
            Some('_') | None => Err(EnvironmentError::CannotImportPrivateSymbol(
                symbol.to_owned(),
            )),
            _ => self.set(new_name, env.get(symbol)?),
        }
    }

    /// Return the parent environment (or `None` if there is no parent).
    pub fn get_parent(&self) -> Option<Environment> {
        self.env.borrow().get_parent()
    }
}

impl EnvironmentContent {
    /// Create a new child environment
    /// Freeze the environment, all its value will become immutable after that
    pub fn freeze(&mut self) {
        if !self.frozen {
            self.frozen = true;
            for v in self.variables.values_mut() {
                v.freeze();
            }
        }
    }

    /// Set the value of a variable in that environment.
    pub fn set(&mut self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        if self.frozen {
            Err(EnvironmentError::TryingToMutateFrozenEnvironment)
        } else {
            self.variables.insert(name.to_string(), value);
            Ok(())
        }
    }

    /// Get the value of the variable `name`
    pub fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        if self.variables.contains_key(name) {
            Ok(self.variables[name].clone())
        } else {
            match self.parent {
                Some(ref p) => p.get(name),
                None => Err(EnvironmentError::VariableNotFound(name.to_owned())),
            }
        }
    }

    /// Get the object of type `obj_type`, and create it if none exists
    pub fn add_type_value(&mut self, obj: &str, attr: &str, value: Value) {
        if let Some(ref mut v) = self.type_objs.get_mut(obj) {
            v.insert(attr.to_owned(), value);
            // Do not use a else case for the borrow checker to realize that type_objs is no
            // longer borrowed when inserting.
            return;
        }
        let mut dict = HashMap::new();
        dict.insert(attr.to_owned(), value);
        self.type_objs.insert(obj.to_owned(), dict);
    }

    /// Get a type value if it exists (e.g. list.index).
    pub fn get_type_value(&self, obj: &Value, id: &str) -> Option<Value> {
        match self.type_objs.get(obj.get_type()) {
            Some(ref d) => match d.get(id) {
                Some(v) => Some(v.clone()),
                None => match self.parent {
                    Some(ref p) => p.get_type_value(obj, id),
                    None => None,
                },
            },
            None => match self.parent {
                Some(ref p) => p.get_type_value(obj, id),
                None => None,
            },
        }
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<String> {
        if let Some(ref d) = self.type_objs.get(obj.get_type()) {
            let mut r = Vec::new();
            for k in d.keys() {
                r.push(k.clone());
            }
            r
        } else if let Some(ref p) = self.parent {
            p.list_type_value(obj)
        } else {
            Vec::new()
        }
    }

    /// Return the parent environment (or `None` if there is no parent).
    pub fn get_parent(&self) -> Option<Environment> {
        self.parent.clone()
    }
}
