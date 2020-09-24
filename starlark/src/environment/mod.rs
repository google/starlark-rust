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

use crate::values::cell::error::ObjectBorrowMutError;
use crate::values::cell::ObjectCell;
use crate::values::error::{RuntimeError, ValueError};
use crate::values::string::rc::RcString;
use crate::values::*;
use std::collections::HashMap;
use std::rc::Rc;

// TODO: move that code in some common error code list?
// CM prefix = Critical Module
const __RESERVED_CM00: &str = "CM00";
const NOT_FOUND_ERROR_CODE: &str = "CM01";
const LOCAL_VARIABLE_REFERENCED_BEFORE_ASSIGNMENT: &str = "CM03";
pub(crate) const LOAD_NOT_SUPPORTED_ERROR_CODE: &str = "CM02";
const CANNOT_IMPORT_ERROR_CODE: &str = "CE02";
const BORROW_ERROR_CODE: &str = "CE03";

#[derive(Debug)]
#[doc(hidden)]
pub enum EnvironmentError {
    /// Variables was no found.
    VariableNotFound(String),
    LocalVariableReferencedBeforeAssignment(String),
    /// Cannot import private symbol, i.e. underscore prefixed
    CannotImportPrivateSymbol(String),
    BorrowMut(ObjectBorrowMutError),
}

impl From<ObjectBorrowMutError> for EnvironmentError {
    fn from(e: ObjectBorrowMutError) -> EnvironmentError {
        EnvironmentError::BorrowMut(e)
    }
}

impl Into<RuntimeError> for EnvironmentError {
    fn into(self) -> RuntimeError {
        RuntimeError {
            code: match self {
                EnvironmentError::VariableNotFound(..) => NOT_FOUND_ERROR_CODE,
                EnvironmentError::CannotImportPrivateSymbol(..) => CANNOT_IMPORT_ERROR_CODE,
                EnvironmentError::LocalVariableReferencedBeforeAssignment(..) => {
                    LOCAL_VARIABLE_REFERENCED_BEFORE_ASSIGNMENT
                }
                EnvironmentError::BorrowMut(..) => BORROW_ERROR_CODE,
            },
            label: match self {
                EnvironmentError::VariableNotFound(..) => "Variable was not found".to_owned(),
                EnvironmentError::LocalVariableReferencedBeforeAssignment(..) => {
                    "Local variable referenced before assignment".to_owned()
                }
                EnvironmentError::CannotImportPrivateSymbol(ref s) => {
                    format!("Symbol '{}' is private", s)
                }
                EnvironmentError::BorrowMut(ref e) => format!("{}", e),
            },
            message: match self {
                EnvironmentError::VariableNotFound(s) => format!("Variable '{}' not found", s),
                EnvironmentError::LocalVariableReferencedBeforeAssignment(ref s) => {
                    format!("Local variable '{}' referenced before assignment", s)
                }
                EnvironmentError::CannotImportPrivateSymbol(s) => {
                    format!("Cannot import private symbol '{}'", s)
                }
                EnvironmentError::BorrowMut(ref e) => {
                    format!("Cannot borrow environment mutably: {}", e)
                }
            },
        }
    }
}

impl From<EnvironmentError> for ValueError {
    fn from(e: EnvironmentError) -> Self {
        ValueError::Runtime(e.into())
    }
}

#[derive(Clone, Debug)]
pub struct Environment {
    env: Rc<ObjectCell<EnvironmentContent>>,
}

#[derive(Debug)]
struct EnvironmentContent {
    /// A name for this environment, used mainly for debugging.
    name_: RcString,
    /// Super environment that represent a higher scope than the current one
    parent: Option<Environment>,
    /// List of variable bindings
    ///
    /// These bindings include methods for native types, e.g. `string.isalnum`.
    variables: HashMap<String, Value>,
    /// When `true`, set `{foo, bar}` literals are allowed.
    set_literals: bool,
}

impl Environment {
    /// Create a new environment
    pub fn new(name: &str) -> Environment {
        Environment {
            env: Rc::new(ObjectCell::new_mutable(EnvironmentContent {
                name_: name.into(),
                parent: None,
                variables: HashMap::new(),
                set_literals: false,
            })),
        }
    }

    /// Create a new child environment for this environment
    pub fn child(&self, name: &str) -> Environment {
        self.freeze();
        Environment {
            env: Rc::new(ObjectCell::new_mutable(EnvironmentContent {
                name_: name.into(),
                parent: Some(self.clone()),
                variables: HashMap::new(),
                set_literals: self.env.borrow().set_literals,
            })),
        }
    }

    /// Create a new child environment
    /// Freeze the environment, all its value will become immutable after that
    pub fn freeze(&self) -> &Self {
        if !self.env.get_header_copy().is_mutable_frozen() {
            self.env.borrow_mut().freeze();
            self.env.freeze();
        }
        self
    }

    /// Return the name of this module
    pub fn name(&self) -> RcString {
        self.env.borrow().name_.clone()
    }

    /// Set the value of a variable in that environment.
    pub fn set(&self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.env.try_borrow_mut()?.set(name, value)
    }

    /// Get the value of the variable `name`
    pub fn get(&self, name: &str) -> Result<Value, EnvironmentError> {
        self.env.borrow().get(name)
    }

    pub fn import_symbol(
        &self,
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

    /// Set the function which will be used to instantiate set literals encountered when evaluating
    /// in this `Environment`. Set literals are {}s with one or more elements between, separated by
    /// commas, e.g. `{1, 2, "three"}`.
    ///
    /// If this function is not called on the `Environment`, its parent's set constructor will be
    /// used when set literals are encountered. If neither this `Environment`, nor any of its
    /// transitive parents, have a set constructor defined, attempts to evaluate set literals will
    /// raise and error.
    ///
    /// The `Value` returned by this function is expected to be a one-dimensional collection
    /// containing no duplicates.
    pub fn enable_set_literals(&self) {
        self.env.borrow_mut().set_literals = true;
    }

    /// Is it OK to have set literals?
    pub(crate) fn set_literals_emabled(&self) -> bool {
        self.env.borrow().set_literals
    }
}

impl EnvironmentContent {
    /// Create a new child environment
    /// Freeze the environment, all its value will become immutable after that
    pub fn freeze(&mut self) {
        for v in self.variables.values_mut() {
            v.freeze();
        }
    }

    /// Set the value of a variable in that environment.
    pub fn set(&mut self, name: &str, value: Value) -> Result<(), EnvironmentError> {
        self.variables.insert(name.to_string(), value);
        Ok(())
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

    /// Return the parent environment (or `None` if there is no parent).
    pub fn get_parent(&self) -> Option<Environment> {
        self.parent.clone()
    }
}

/// Environment passed to `call` calls.
///
/// Function implementations are only allowed to access
/// type values from "type values" from the caller context,
/// so this struct is passed instead of full `Environment`.
#[derive(Clone, Default, Debug)]
pub struct TypeValues {
    /// List of static values of an object per type
    type_objs: HashMap<RcString, HashMap<RcString, Value>>,
}

impl TypeValues {
    /// Get a type value if it exists (e.g. list.index).
    pub fn get_type_value(&self, obj: &Value, id: &str) -> Option<Value> {
        self.type_objs
            .get(obj.get_type())
            .and_then(|o| o.get(id))
            .cloned()
    }

    /// List the attribute of a type
    pub fn list_type_value(&self, obj: &Value) -> Vec<RcString> {
        self.type_objs
            .get(obj.get_type())
            .into_iter()
            .flat_map(|o| o.keys().cloned())
            .collect()
    }

    /// Get the object of type `obj_type`, and create it if none exists
    pub fn add_type_value(&mut self, obj: &str, attr: &str, value: Value) {
        if let Some(ref mut v) = self.type_objs.get_mut(obj) {
            v.insert(attr.into(), value);
        } else {
            let mut dict = HashMap::new();
            dict.insert(attr.into(), value);
            self.type_objs.insert(obj.into(), dict);
        }
    }
}
