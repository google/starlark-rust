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
use crate::stdlib::macros::param::TryParamConvertFromValue;
use crate::values::error::RuntimeError;
use crate::values::none::NoneType;
use std::convert::TryInto;
use std::iter;
use std::mem;
use std::vec;

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
pub struct FunctionSignature {
    params: Vec<FunctionParameter>,
    /// Number of leading positional-only parameters
    positional_count: usize,
}

impl FunctionSignature {
    pub(crate) fn new(
        parameters: Vec<FunctionParameter>,
        positional_count: usize,
    ) -> FunctionSignature {
        FunctionSignature {
            params: parameters,
            positional_count,
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a FunctionParameter, bool)> + 'a {
        let positional_count = self.positional_count;
        self.params
            .iter()
            .enumerate()
            .map(move |(i, p)| (p, i < positional_count))
    }
}

#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum FunctionType {
    Native(String),
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
    dyn Fn(&CallStack, TypeValues, Vec<FunctionArg>) -> ValueResult;

/// Function implementation for native (written in Rust) functions.
///
/// Public to be referenced in macros.
#[doc(hidden)]
pub struct NativeFunction {
    /// Pointer to a native function.
    /// Note it is a function pointer, not `Box<Fn(...)>`
    /// to avoid generic instantiation and allocation for each native function.
    function: fn(&mut CallStack, TypeValues, ParameterParser) -> ValueResult,
    signature: FunctionSignature,
    function_type: FunctionType,
}

// Wrapper for method that have been affected the self object
pub(crate) struct WrappedMethod {
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
        signature: FunctionSignature,
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

impl From<FunctionError> for ValueError {
    fn from(e: FunctionError) -> Self {
        ValueError::Runtime(e.into())
    }
}

impl NativeFunction {
    pub fn new(
        name: String,
        function: fn(&mut CallStack, TypeValues, ParameterParser) -> ValueResult,
        signature: FunctionSignature,
    ) -> Value {
        Value::new(NativeFunction {
            function,
            signature,
            function_type: FunctionType::Native(name),
        })
    }
}

impl WrappedMethod {
    pub fn new(self_obj: Value, method: Value) -> Value {
        Value::new(WrappedMethod { method, self_obj })
    }
}

impl FunctionType {
    fn to_str(&self) -> String {
        match self {
            FunctionType::Native(ref name) => name.clone(),
            FunctionType::Def(ref name, ..) => name.clone(),
        }
    }

    fn to_repr(&self) -> String {
        match self {
            FunctionType::Native(ref name) => format!("<native function {}>", name),
            FunctionType::Def(ref name, ref module, ..) => {
                format!("<function {} from {}>", name, module)
            }
        }
    }
}

pub(crate) enum StrOrRepr {
    Str,
    Repr,
}

pub(crate) fn str_impl(
    buf: &mut String,
    function_type: &FunctionType,
    signature: &FunctionSignature,
    str_or_repr: StrOrRepr,
) -> fmt::Result {
    write!(
        buf,
        "{}",
        match str_or_repr {
            StrOrRepr::Str => function_type.to_str(),
            StrOrRepr::Repr => function_type.to_repr(),
        }
    )?;
    write!(buf, "(")?;

    for (i, x) in signature.params.iter().enumerate() {
        if i != 0 && i == signature.positional_count {
            write!(buf, ", /")?;
        }

        if i != 0 {
            write!(buf, ", ")?;
        }

        match x {
            FunctionParameter::Normal(ref name) => write!(buf, "{}", name)?,
            FunctionParameter::Optional(ref name) => write!(buf, "?{}", name)?,
            FunctionParameter::WithDefaultValue(ref name, ref value) => {
                write!(buf, "{} = {}", name, value.to_repr())?;
            }
            FunctionParameter::ArgsArray(ref name) => write!(buf, "*{}", name)?,
            FunctionParameter::KWArgsDict(ref name) => write!(buf, "**{}", name)?,
        }
    }

    if signature.positional_count != 0 && signature.positional_count == signature.params.len() {
        write!(buf, ", /")?;
    }

    write!(buf, ")")?;
    Ok(())
}

pub(crate) fn repr(function_type: &FunctionType, signature: &FunctionSignature) -> String {
    let mut buf = String::new();
    str_impl(&mut buf, function_type, signature, StrOrRepr::Repr).unwrap();
    buf
}

#[doc(hidden)]
pub struct ParameterParser<'a> {
    signature: &'a FunctionSignature,
    // current parameter index in function signature
    index: usize,
    function_type: &'a FunctionType,
    positional: vec::IntoIter<Value>,
    kwargs: LinkedHashMap<String, Value>,
}

impl<'a> ParameterParser<'a> {
    pub fn new(
        signature: &'a FunctionSignature,
        function_type: &'a FunctionType,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs_arg: Option<Value>,
    ) -> Result<ParameterParser<'a>, ValueError> {
        // Collect args
        let mut av = positional;
        if let Some(x) = args {
            match x.iter() {
                Ok(y) => av.extend(y.iter()),
                Err(..) => return Err(FunctionError::ArgsArrayIsNotIterable.into()),
            }
        };
        let positional = av.into_iter();
        // Collect kwargs
        let mut kwargs = named;
        if let Some(x) = kwargs_arg {
            match x.iter() {
                Ok(y) => {
                    for n in &y {
                        if n.get_type() == "string" {
                            let k = n.to_str();
                            if let Ok(v) = x.at(n) {
                                kwargs.insert(k, v);
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

        Ok(ParameterParser {
            signature,
            index: 0,
            function_type,
            positional,
            kwargs,
        })
    }

    pub fn next_normal(&mut self, name: &str, positional_only: bool) -> Result<Value, ValueError> {
        if let Some(x) = self.positional.next() {
            self.index += 1;
            return Ok(x);
        }

        if !positional_only {
            if let Some(ref r) = self.kwargs.remove(name) {
                self.index += 1;
                return Ok(r.clone());
            }
        }

        Err(FunctionError::NotEnoughParameter {
            missing: name.to_string(),
            function_type: self.function_type.clone(),
            signature: self.signature.clone(),
        }
        .into())
    }

    pub fn next_optional(&mut self, name: &str, positional_only: bool) -> Option<Value> {
        self.index += 1;
        if let Some(x) = self.positional.next() {
            return Some(x);
        }

        if !positional_only {
            if let Some(ref r) = self.kwargs.remove(name) {
                return Some(r.clone());
            }
        }

        None
    }

    pub fn next_with_default_value(
        &mut self,
        name: &str,
        positional_only: bool,
        default_value: &Value,
    ) -> Value {
        self.next_optional(name, positional_only)
            .unwrap_or_else(|| default_value.clone())
    }

    pub fn next_args_array(&mut self) -> Vec<Value> {
        self.index += 1;
        mem::replace(&mut self.positional, Vec::new().into_iter()).collect()
    }

    pub fn next_kwargs_dict(&mut self) -> LinkedHashMap<String, Value> {
        self.index += 1;
        mem::replace(&mut self.kwargs, Default::default())
    }

    pub fn check_no_more_args(&mut self) -> Result<(), ValueError> {
        if self.positional.next().is_some() || !self.kwargs.is_empty() {
            return Err(FunctionError::ExtraParameter.into());
        }
        debug_assert_eq!(self.index, self.signature.params.len());
        Ok(())
    }

    /// This function is only called from macros
    pub fn next_arg(&mut self) -> Result<FunctionArg, ValueError> {
        // Macros call this function exactly once for each signature item.
        // So it's safe to panic here.
        assert!(self.index != self.signature.params.len());
        let positional_only = self.index < self.signature.positional_count;
        Ok(match &self.signature.params[self.index] {
            FunctionParameter::Normal(ref name) => {
                FunctionArg::Normal(self.next_normal(name, positional_only)?)
            }
            FunctionParameter::Optional(ref name) => {
                FunctionArg::Optional(self.next_optional(name, positional_only))
            }
            FunctionParameter::WithDefaultValue(ref name, ref value) => {
                FunctionArg::Normal(self.next_with_default_value(name, positional_only, value))
            }
            FunctionParameter::ArgsArray(..) => FunctionArg::ArgsArray(self.next_args_array()),
            FunctionParameter::KWArgsDict(..) => FunctionArg::KWArgsDict(self.next_kwargs_dict()),
        })
    }
}

/// Define the function type
impl TypedValue for NativeFunction {
    type Holder = Immutable<NativeFunction>;

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(iter::empty())
    }

    fn to_str_impl(&self, buf: &mut String) -> fmt::Result {
        str_impl(buf, &self.function_type, &self.signature, StrOrRepr::Str)
    }
    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        str_impl(buf, &self.function_type, &self.signature, StrOrRepr::Repr)
    }

    const TYPE: &'static str = "function";

    fn call(
        &self,
        call_stack: &mut CallStack,
        type_values: TypeValues,
        positional: Vec<Value>,
        named: LinkedHashMap<String, Value>,
        args: Option<Value>,
        kwargs: Option<Value>,
    ) -> ValueResult {
        let parser = ParameterParser::new(
            &self.signature,
            &self.function_type,
            positional,
            named,
            args,
            kwargs,
        )?;

        (self.function)(call_stack, type_values, parser)
    }
}

impl TypedValue for WrappedMethod {
    type Holder = Immutable<WrappedMethod>;

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(vec![self.method.clone(), self.self_obj.clone()].into_iter())
    }

    fn function_id(&self) -> Option<FunctionId> {
        Some(FunctionId(self.method.data_ptr()))
    }

    fn to_str_impl(&self, buf: &mut String) -> fmt::Result {
        self.method.to_str_impl(buf)
    }
    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        self.method.to_repr_impl(buf)
    }
    const TYPE: &'static str = "function";

    fn call(
        &self,
        call_stack: &mut CallStack,
        type_values: TypeValues,
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
            .call(call_stack, type_values, positional, named, args, kwargs)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::values::function::{FunctionParameter, FunctionSignature, FunctionType};

    #[test]
    fn fmt_signature_positional() {
        assert_eq!(
            "<native function f>()",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(vec![], 0)
            )
        );
        assert_eq!(
            "<native function f>(a)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(vec![FunctionParameter::Normal("a".to_owned())], 0)
            )
        );
        assert_eq!(
            "<native function f>(a, /)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(vec![FunctionParameter::Normal("a".to_owned())], 1)
            )
        );
        assert_eq!(
            "<native function f>(a, b)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(
                    vec![
                        FunctionParameter::Normal("a".to_owned()),
                        FunctionParameter::Normal("b".to_owned()),
                    ],
                    0,
                )
            )
        );
        assert_eq!(
            "<native function f>(a, /, b)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(
                    vec![
                        FunctionParameter::Normal("a".to_owned()),
                        FunctionParameter::Normal("b".to_owned()),
                    ],
                    1,
                )
            )
        );
        assert_eq!(
            "<native function f>(a, b, /)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(
                    vec![
                        FunctionParameter::Normal("a".to_owned()),
                        FunctionParameter::Normal("b".to_owned()),
                    ],
                    2,
                )
            )
        );
        assert_eq!(
            "<native function f>(a, b, /, **k)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(
                    vec![
                        FunctionParameter::Normal("a".to_owned()),
                        FunctionParameter::Normal("b".to_owned()),
                        FunctionParameter::KWArgsDict("k".to_owned()),
                    ],
                    2,
                )
            )
        );
    }

    #[test]
    fn fmt_signature_optional() {
        assert_eq!(
            "<native function f>(?a)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(vec![FunctionParameter::Optional("a".to_owned())], 0)
            )
        );
        assert_eq!(
            "<native function f>(?a, /)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(vec![FunctionParameter::Optional("a".to_owned())], 1)
            )
        );
    }

    #[test]
    fn fmt_signature_with_default_value() {
        assert_eq!(
            "<native function f>(a = 10)",
            repr(
                &FunctionType::Native("f".to_owned()),
                &FunctionSignature::new(
                    vec![FunctionParameter::WithDefaultValue(
                        "a".to_owned(),
                        Value::new(10),
                    )],
                    0,
                )
            )
        );
    }
}
