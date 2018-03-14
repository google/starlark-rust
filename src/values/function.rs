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

//! Function as a TypedValue
use super::*;
use syntax::ast::AstStatement;
use environment::Environment;
use eval::eval_def;

#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum FunctionParameter {
    Normal(String),
    WithDefaultValue(String, Value),
    ArgsArray(String),
    KWArgsDict(String),
}

#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum FunctionType {
    Native(String),
    NativeMethod(String, String),
    Def(String, String),
}

pub struct Function {
    function: Box<Fn(&Vec<String>, Environment, Vec<Value>) -> ValueResult>,
    signature: Vec<FunctionParameter>,
    function_type: FunctionType,
}

// Wrapper for method that have been affected the self object
struct WrappedMethod {
    method: Value,
    self_obj: Value,
}

// TODO: move that code in some common error code list?
// CV prefix = Critical Function call
const NOT_ENOUGH_PARAMS_ERROR_CODE: &'static str = "CF00";
const WRONG_ARGS_IDENT_ERROR_CODE: &'static str = "CF01";
const ARGS_NOT_ITERABLE_ERROR_CODE: &'static str = "CF02";
const KWARGS_NOT_MAPPABLE_ERROR_CODE: &'static str = "CF03";
const KWARGS_KEY_IDENT_ERROR_CODE: &'static str = "CF04";
const EXTRA_PARAMETER_ERROR_CODE: &'static str = "CF05";

#[derive(Debug, Clone)]
pub enum FunctionError {
    NotEnoughParameter {
        missing: String,
        function_type: FunctionType,
        signature: Vec<FunctionParameter>,
    },
    ArgsValueIsNotString,
    ArgsArrayIsNotIterable,
    KWArgsDictIsNotMappable,
    KWArgsKeyIsNotAValidIdentifier(String),
    ExtraParameter,
}

impl Into<RuntimeError> for FunctionError {
    fn into(self) -> RuntimeError {
        RuntimeError {
            code: match self {
                FunctionError::NotEnoughParameter { .. } => NOT_ENOUGH_PARAMS_ERROR_CODE,
                FunctionError::ArgsValueIsNotString => WRONG_ARGS_IDENT_ERROR_CODE,
                FunctionError::ArgsArrayIsNotIterable => ARGS_NOT_ITERABLE_ERROR_CODE,
                FunctionError::KWArgsDictIsNotMappable => KWARGS_NOT_MAPPABLE_ERROR_CODE,
                FunctionError::KWArgsKeyIsNotAValidIdentifier(..) => KWARGS_KEY_IDENT_ERROR_CODE,
                FunctionError::ExtraParameter => EXTRA_PARAMETER_ERROR_CODE,
            },
            label: match self {
                FunctionError::NotEnoughParameter { .. } => {
                    "Not enough parameters in function call".to_owned()
                }
                FunctionError::ArgsValueIsNotString => "not an identifier for *args".to_owned(),
                FunctionError::ArgsArrayIsNotIterable => "*args is not iterable".to_owned(),
                FunctionError::KWArgsDictIsNotMappable => "**kwargs is not mappable".to_owned(),
                FunctionError::KWArgsKeyIsNotAValidIdentifier(..) => {
                    "Incorrect key in **kwargs".to_owned()
                }
                FunctionError::ExtraParameter => "Extraneous parameter in function call".to_owned(),
            },
            message: match self {
                FunctionError::NotEnoughParameter {
                    missing,
                    function_type,
                    signature,
                } => {
                    format!(
                        "Missing parameter {} for call to {}",
                        missing.trim_left_matches("$"),
                        repr(&function_type, &signature)
                    )
                }
                FunctionError::ArgsValueIsNotString => {
                    "The argument provided for *args is not an identifier".to_owned()
                }
                FunctionError::ArgsArrayIsNotIterable => {
                    "The argument provided for *args is not iterable".to_owned()
                }
                FunctionError::KWArgsDictIsNotMappable => {
                    "The argument provided for **kwargs is not mappable".to_owned()
                }
                FunctionError::KWArgsKeyIsNotAValidIdentifier(k) => {
                    format!(
                        concat!(
                            "The **kwargs dictionary contains a key '{}'",
                            " that is not a correct identifier"
                        ),
                        k
                    )
                }
                FunctionError::ExtraParameter => {
                    "Extraneous parameter passed to function call".to_owned()
                }
            },
        }
    }
}

impl Into<ValueError> for FunctionError {
    fn into(self) -> ValueError {
        ValueError::Runtime(self.into())
    }
}

macro_rules! check_identifier {
    ($arg: expr) => {
        {
            $arg.char_indices().all(|x| (x.0 != 0 || !x.1.is_digit(10)) && (
                x.1 == '_' || x.1.is_digit(10) || x.1.is_alphabetic()))
        }
    }
}

impl Function {
    pub fn new<F>(name: String, f: F, signature: Vec<FunctionParameter>) -> Value
    where
        F: Fn(&Vec<String>, Environment, Vec<Value>) -> ValueResult + 'static,
    {
        Value::new(Function {
            function: Box::new(f),
            signature: signature,
            function_type: FunctionType::Native(name),
        })
    }

    pub fn new_method<F>(
        objname: String,
        name: String,
        f: F,
        signature: Vec<FunctionParameter>,
    ) -> Value
    where
        F: Fn(&Vec<String>, Environment, Vec<Value>) -> ValueResult + 'static,
    {
        Value::new(Function {
            function: Box::new(f),
            signature,
            function_type: FunctionType::NativeMethod(objname, name),
        })
    }

    pub fn new_def(
        name: String,
        module: String,
        signature: Vec<FunctionParameter>,
        stmts: AstStatement,
    ) -> Value {
        let signature_cp = signature.clone();
        Value::new(Function {
            function: Box::new(move |stack, env, v| {
                eval_def(stack, &signature_cp, &stmts, env, v)
            }),
            signature,
            function_type: FunctionType::Def(name, module),
        })
    }

    pub fn new_self_call(self_obj: Value, method: Value) -> Value {
        Value::new(WrappedMethod { method, self_obj })
    }
}

impl FunctionType {
    fn to_str(&self) -> String {
        match self {
            &FunctionType::Native(ref name) => format!("<native function {}>", name),
            &FunctionType::NativeMethod(ref function_type, ref name) => {
                format!("<native method {}.{}>", function_type, name)
            }
            &FunctionType::Def(ref name, ref module, ..) => {
                format!("<function {} from {}>", name, module)
            }
        }
    }
}

fn repr(function_type: &FunctionType, signature: &Vec<FunctionParameter>) -> String {
    let v: Vec<String> = signature
        .iter()
        .map(|x| -> String {
            match x {
                &FunctionParameter::Normal(ref name) => name.clone(),
                &FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    format!("{} = {}", name, value.to_repr())
                }
                &FunctionParameter::ArgsArray(ref name) => format!("*{}", name),
                &FunctionParameter::KWArgsDict(ref name) => format!("**{}", name),
            }
        })
        .collect();
    format!("{}: ({})", function_type.to_str(), v.join(", "))
}

/// Define the function type
impl TypedValue for Function {
    immutable!();
    any!();

    fn to_str(&self) -> String {
        self.function_type.to_str()
    }
    fn to_repr(&self) -> String {
        repr(&self.function_type, &self.signature)
    }

    not_supported!(to_int);
    fn get_type(&self) -> &'static str {
        "function"
    }
    fn to_bool(&self) -> bool {
        true
    }
    not_supported!(get_hash);

    fn compare(&self, other: Value) -> Ordering {
        if other.get_type() == "function" {
            self.to_repr().cmp(&other.to_repr())
        } else {
            default_compare(self, other)
        }
    }

    fn call(
        &self,
        call_stack: &Vec<String>,
        env: Environment,
        positional: Vec<Value>,
        named: HashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        // First map arguments to a vector
        let mut v = Vec::new();
        // Collect args
        let av: Vec<Value> = if let Some(x) = args {
            match x.into_iter() {
                Ok(y) => positional.into_iter().chain(y).collect(),
                Err(..) => return Err(FunctionError::ArgsArrayIsNotIterable.into()),
            }
        } else {
            positional.into_iter().collect()
        };
        let mut args_iter = av.into_iter();
        // Collect kwargs
        let mut kwargs_dict = named.clone();
        if let Some(x) = kwargs {
            match x.into_iter() {
                Ok(y) => {
                    for n in y {
                        if n.get_type() == "string" {
                            let k = n.to_str();
                            if !check_identifier!(k) {
                                return Err(FunctionError::KWArgsKeyIsNotAValidIdentifier(k).into());
                            } else {
                                if let Ok(v) = x.at(n) {
                                    kwargs_dict.insert(k, v);
                                } else {
                                    return Err(FunctionError::KWArgsDictIsNotMappable.into());
                                }
                            }
                        } else {
                            return Err(FunctionError::ArgsValueIsNotString.into());
                        }
                    }
                }
                Err(..) => return Err(FunctionError::KWArgsDictIsNotMappable.into()),
            }
        }
        // Now verify signature and transform in a value vector
        for parameter in self.signature.iter() {
            match parameter {
                &FunctionParameter::Normal(ref name) => {
                    if let Some(x) = args_iter.next() {
                        v.push(x)
                    } else {
                        if let Some(ref r) = kwargs_dict.remove(name) {
                            v.push(r.clone());
                        } else {
                            return Err(
                                FunctionError::NotEnoughParameter {
                                    missing: name.to_string(),
                                    function_type: self.function_type.clone(),
                                    signature: self.signature.clone(),
                                }.into(),
                            );
                        }
                    }
                }
                &FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    if let Some(x) = args_iter.next() {
                        v.push(x)
                    } else {
                        if let Some(ref r) = kwargs_dict.remove(name) {
                            v.push(r.clone());
                        } else {
                            v.push(value.clone());
                        }
                    }
                }
                &FunctionParameter::ArgsArray(..) => {
                    let argv: Vec<Value> = args_iter.clone().collect();
                    v.push(Value::from(argv));
                    // We do not use last so we keep ownership of the iterator
                    while args_iter.next().is_some() {}
                }
                &FunctionParameter::KWArgsDict(..) => {
                    v.push(Value::from(kwargs_dict.clone()));
                    kwargs_dict.clear();
                }
            }
        }
        if args_iter.next().is_some() || !kwargs_dict.is_empty() {
            return Err(FunctionError::ExtraParameter.into());
        }
        // Finally call the function with a new child environment
        (*self.function)(
            call_stack,
            env.child(&format!("{}#{}", env.name(), &self.to_str())),
            v,
        )
    }

    not_supported!(binop);
    not_supported!(container);
}

impl TypedValue for WrappedMethod {
    immutable!();
    any!();

    fn to_str(&self) -> String {
        self.method.to_str()
    }
    fn to_repr(&self) -> String {
        self.method.to_repr()
    }
    fn get_type(&self) -> &'static str {
        "function"
    }
    fn to_bool(&self) -> bool {
        true
    }
    fn compare(&self, other: Value) -> Ordering {
        self.method.compare(other)
    }

    fn call(
        &self,
        call_stack: &Vec<String>,
        env: Environment,
        positional: Vec<Value>,
        named: HashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        // The only thing that this wrapper does is insert self at the beginning of the positional
        // vector
        let positional: Vec<Value> = Some(self.self_obj.clone())
            .into_iter()
            .chain(positional.into_iter())
            .collect();
        self.method.call(
            call_stack,
            env,
            positional,
            named,
            args,
            kwargs,
        )
    }

    not_supported!(to_int, get_hash);
    not_supported!(binop);
    not_supported!(container);
}
