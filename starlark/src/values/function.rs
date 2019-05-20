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
use crate::environment::Environment;
use crate::eval::eval_def;
use crate::stdlib::macros::param::TryParamConvertFromValue;
use crate::syntax::ast::AstStatement;
use crate::values::error::RuntimeError;
use crate::values::none::NoneType;
use codemap::CodeMap;
use std::convert::TryInto;
use std::mem;
use std::sync::{Arc, Mutex};

#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum FunctionParameter {
    Normal(String),
    Optional(String),
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

#[derive(Debug, Clone)]
pub enum FunctionArg {
    Normal(Value),
    Optional(Option<Value>),
    ArgsArray(Vec<Value>),
    KWArgsDict(LinkedHashMap<String, Value>),
}

impl FunctionArg {
    pub fn into_normal<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<T, ValueError> {
        match self {
            FunctionArg::Normal(v) => {
                T::try_from(v).map_err(|_| ValueError::IncorrectParameterTypeNamed(param_name))
            }
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_optional<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<Option<T>, ValueError> {
        match self {
            FunctionArg::Optional(Some(v)) => {
                Ok(Some(T::try_from(v).map_err(|_| {
                    ValueError::IncorrectParameterTypeNamed(param_name)
                })?))
            }
            FunctionArg::Optional(None) => Ok(None),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_args_array<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<Vec<T>, ValueError> {
        match self {
            FunctionArg::ArgsArray(v) => Ok(v
                .into_iter()
                .map(T::try_from)
                .collect::<Result<Vec<T>, _>>()
                .map_err(|_| ValueError::IncorrectParameterTypeNamed(param_name))?),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }

    pub fn into_kw_args_dict<T: TryParamConvertFromValue>(
        self,
        param_name: &'static str,
    ) -> Result<LinkedHashMap<String, T>, ValueError> {
        match self {
            FunctionArg::KWArgsDict(dict) => Ok({
                let mut r = LinkedHashMap::new();
                for (k, v) in dict {
                    r.insert(
                        k,
                        T::try_from(v)
                            .map_err(|_| ValueError::IncorrectParameterTypeNamed(param_name))?,
                    );
                }
                r
            }),
            _ => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl From<FunctionArg> for Value {
    fn from(a: FunctionArg) -> Value {
        match a {
            FunctionArg::Normal(v) => v,
            FunctionArg::ArgsArray(v) => v.into(),
            FunctionArg::Optional(v) => match v {
                Some(v) => v,
                None => Value::new(NoneType::None),
            },
            FunctionArg::KWArgsDict(v) => {
                // `unwrap` does not panic, because key is a string which hashable
                v.try_into().unwrap()
            }
        }
    }
}

pub type StarlarkFunctionPrototype =
    dyn Fn(&[(String, String)], Environment, Vec<FunctionArg>) -> ValueResult;

pub struct Function {
    function: Box<StarlarkFunctionPrototype>,
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
const NOT_ENOUGH_PARAMS_ERROR_CODE: &str = "CF00";
const WRONG_ARGS_IDENT_ERROR_CODE: &str = "CF01";
const ARGS_NOT_ITERABLE_ERROR_CODE: &str = "CF02";
const KWARGS_NOT_MAPPABLE_ERROR_CODE: &str = "CF03";
// Not an error: const KWARGS_KEY_IDENT_ERROR_CODE: &str = "CF04";
const EXTRA_PARAMETER_ERROR_CODE: &str = "CF05";

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
                FunctionError::ExtraParameter => EXTRA_PARAMETER_ERROR_CODE,
            },
            label: match self {
                FunctionError::NotEnoughParameter { .. } => {
                    "Not enough parameters in function call".to_owned()
                }
                FunctionError::ArgsValueIsNotString => "not an identifier for *args".to_owned(),
                FunctionError::ArgsArrayIsNotIterable => "*args is not iterable".to_owned(),
                FunctionError::KWArgsDictIsNotMappable => "**kwargs is not mappable".to_owned(),
                FunctionError::ExtraParameter => "Extraneous parameter in function call".to_owned(),
            },
            message: match self {
                FunctionError::NotEnoughParameter {
                    missing,
                    function_type,
                    signature,
                } => format!(
                    "Missing parameter {} for call to {}",
                    missing.trim_start_matches('$'),
                    repr(&function_type, &signature)
                ),
                FunctionError::ArgsValueIsNotString => {
                    "The argument provided for *args is not an identifier".to_owned()
                }
                FunctionError::ArgsArrayIsNotIterable => {
                    "The argument provided for *args is not iterable".to_owned()
                }
                FunctionError::KWArgsDictIsNotMappable => {
                    "The argument provided for **kwargs is not mappable".to_owned()
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

impl Function {
    #[allow(clippy::new_ret_no_self)]
    pub fn new<F>(name: String, f: F, signature: Vec<FunctionParameter>) -> Value
    where
        F: Fn(&[(String, String)], Environment, Vec<FunctionArg>) -> ValueResult + 'static,
    {
        Value::new(Function {
            function: Box::new(f),
            signature,
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
        F: Fn(&[(String, String)], Environment, Vec<FunctionArg>) -> ValueResult + 'static,
    {
        Value::new(Function {
            function: Box::new(f),
            signature,
            function_type: FunctionType::NativeMethod(objname, name),
        })
    }

    #[allow(clippy::boxed_local)]
    pub fn new_def(
        name: String,
        module: String,
        signature: Vec<FunctionParameter>,
        stmts: AstStatement,
        map: Arc<Mutex<CodeMap>>,
        env: Environment,
    ) -> Value {
        let signature_cp = signature.clone();
        let name_for_closure = name.clone();
        Value::new(Function {
            function: Box::new(move |stack, globals, v| {
                eval_def(
                    &name_for_closure,
                    stack,
                    &signature_cp,
                    &stmts,
                    env.clone(),
                    globals,
                    v,
                    map.clone(),
                )
            }),
            signature,
            function_type: FunctionType::Def(name, module),
        })
    }

    pub fn new_self_call(self_obj: Value, method: Value) -> Value {
        Value::new(WrappedMethod { method, self_obj })
    }

    pub fn name(&self) -> String {
        self.function_type.to_str()
    }
}

impl FunctionType {
    fn to_str(&self) -> String {
        match self {
            FunctionType::Native(ref name) => name.clone(),
            FunctionType::NativeMethod(ref function_type, ref name) => {
                format!("{}.{}", function_type, name)
            }
            FunctionType::Def(ref name, ..) => name.clone(),
        }
    }

    fn to_repr(&self) -> String {
        match self {
            FunctionType::Native(ref name) => format!("<native function {}>", name),
            FunctionType::NativeMethod(ref function_type, ref name) => {
                format!("<native method {}.{}>", function_type, name)
            }
            FunctionType::Def(ref name, ref module, ..) => {
                format!("<function {} from {}>", name, module)
            }
        }
    }
}

fn repr(function_type: &FunctionType, signature: &[FunctionParameter]) -> String {
    let v: Vec<String> = signature
        .iter()
        .map(|x| -> String {
            match x {
                FunctionParameter::Normal(ref name) => name.clone(),
                FunctionParameter::Optional(ref name) => format!("?{}", name),
                FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    format!("{} = {}", name, value.to_repr())
                }
                FunctionParameter::ArgsArray(ref name) => format!("*{}", name),
                FunctionParameter::KWArgsDict(ref name) => format!("**{}", name),
            }
        })
        .collect();
    format!("{}({})", function_type.to_repr(), v.join(", "))
}

fn to_str(function_type: &FunctionType, signature: &[FunctionParameter]) -> String {
    let v: Vec<String> = signature
        .iter()
        .map(|x| -> String {
            match x {
                FunctionParameter::Normal(ref name) => name.clone(),
                FunctionParameter::Optional(ref name) => name.clone(),
                FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    format!("{} = {}", name, value.to_repr())
                }
                FunctionParameter::ArgsArray(ref name) => format!("*{}", name),
                FunctionParameter::KWArgsDict(ref name) => format!("**{}", name),
            }
        })
        .collect();
    format!("{}({})", function_type.to_str(), v.join(", "))
}

/// Define the function type
impl TypedValue for Function {
    immutable!();
    any!();

    fn to_str(&self) -> String {
        to_str(&self.function_type, &self.signature)
    }
    fn to_repr(&self) -> String {
        repr(&self.function_type, &self.signature)
    }

    fn get_type(&self) -> &'static str {
        "function"
    }

    fn call(
        &self,
        call_stack: &[(String, String)],
        globals: Environment,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        // First map arguments to a vector
        let mut v = Vec::new();
        // Collect args
        let mut av = positional;
        if let Some(x) = args {
            match x.iter() {
                Ok(y) => av.extend(y),
                Err(..) => return Err(FunctionError::ArgsArrayIsNotIterable.into()),
            }
        };
        let mut args_iter = av.into_iter();
        // Collect kwargs
        let mut kwargs_dict = named;
        if let Some(x) = kwargs {
            match x.iter() {
                Ok(y) => {
                    for n in y {
                        if n.get_type() == "string" {
                            let k = n.to_str();
                            if let Ok(v) = x.at(n) {
                                kwargs_dict.insert(k, v);
                            } else {
                                return Err(FunctionError::KWArgsDictIsNotMappable.into());
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
                FunctionParameter::Normal(ref name) => {
                    if let Some(x) = args_iter.next() {
                        v.push(FunctionArg::Normal(x))
                    } else if let Some(ref r) = kwargs_dict.remove(name) {
                        v.push(FunctionArg::Normal(r.clone()));
                    } else {
                        return Err(FunctionError::NotEnoughParameter {
                            missing: name.to_string(),
                            function_type: self.function_type.clone(),
                            signature: self.signature.clone(),
                        }
                        .into());
                    }
                }
                FunctionParameter::Optional(ref name) => {
                    if let Some(x) = args_iter.next() {
                        v.push(FunctionArg::Optional(Some(x)))
                    } else if let Some(ref r) = kwargs_dict.remove(name) {
                        v.push(FunctionArg::Optional(Some(r.clone())));
                    } else {
                        v.push(FunctionArg::Optional(None));
                    }
                }
                FunctionParameter::WithDefaultValue(ref name, ref value) => {
                    if let Some(x) = args_iter.next() {
                        v.push(FunctionArg::Normal(x))
                    } else if let Some(ref r) = kwargs_dict.remove(name) {
                        v.push(FunctionArg::Normal(r.clone()));
                    } else {
                        v.push(FunctionArg::Normal(value.clone()));
                    }
                }
                FunctionParameter::ArgsArray(..) => {
                    let argv: Vec<Value> = args_iter.clone().collect();
                    v.push(FunctionArg::ArgsArray(argv));
                    // We do not use last so we keep ownership of the iterator
                    while args_iter.next().is_some() {}
                }
                FunctionParameter::KWArgsDict(..) => {
                    v.push(FunctionArg::KWArgsDict(mem::replace(
                        &mut kwargs_dict,
                        Default::default(),
                    )));
                }
            }
        }
        if args_iter.next().is_some() || !kwargs_dict.is_empty() {
            return Err(FunctionError::ExtraParameter.into());
        }
        // Finally call the function with a new child environment
        (*self.function)(call_stack, globals, v)
    }

    fn is_descendant(&self, _other: &TypedValue) -> bool {
        false
    }
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

    fn call(
        &self,
        call_stack: &[(String, String)],
        env: Environment,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        // The only thing that this wrapper does is insert self at the beginning of the positional
        // vector
        let positional: Vec<Value> = Some(self.self_obj.clone())
            .into_iter()
            .chain(positional.into_iter())
            .collect();
        self.method
            .call(call_stack, env, positional, named, args, kwargs)
    }

    fn is_descendant(&self, _other: &TypedValue) -> bool {
        false
    }
}
