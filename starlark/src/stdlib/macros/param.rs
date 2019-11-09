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

//! Parameter conversion utilities for `starlark_module!` macros.

use crate::values::dict::Dictionary;
use crate::values::error::ValueError;
use crate::values::{TypedValue, Value};
use linked_hash_map::LinkedHashMap;
use std::convert::TryInto;
use std::hash::Hash;

/// Types implementing this type may appear in function parameter types
/// in `starlark_module!` macro function signatures.
pub trait TryParamConvertFromValue: Sized {
    fn try_from(source: Value) -> Result<Self, ValueError>;
}

impl<T: TryParamConvertFromValue> TryParamConvertFromValue for Vec<T> {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        let mut r = Vec::new();
        for item in &source.iter()? {
            r.push(T::try_from(item)?);
        }
        Ok(r)
    }
}

impl<K: TryParamConvertFromValue + Hash + Eq, V: TryParamConvertFromValue> TryParamConvertFromValue
    for LinkedHashMap<K, V>
{
    fn try_from(source: Value) -> Result<Self, ValueError> {
        match source.downcast_ref::<Dictionary>() {
            Some(dict) => {
                let mut r = LinkedHashMap::new();
                for (k, v) in dict.get_content() {
                    r.insert(K::try_from(k.get_value().clone())?, V::try_from(v.clone())?);
                }
                Ok(r)
            }
            None => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl TryParamConvertFromValue for Value {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        Ok(source)
    }
}

impl<T: TypedValue + Clone + 'static> TryParamConvertFromValue for T {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        match source.downcast_ref::<T>() {
            Some(t) => Ok(t.clone()),
            None => Err(ValueError::IncorrectParameterType),
        }
    }
}

impl TryParamConvertFromValue for i32 {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        let source = i64::try_from(source)?;
        source
            .try_into()
            .map_err(|_| ValueError::IncorrectParameterType)
    }
}

impl TryParamConvertFromValue for u32 {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        let source = i64::try_from(source)?;
        source
            .try_into()
            .map_err(|_| ValueError::IncorrectParameterType)
    }
}

impl TryParamConvertFromValue for u64 {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        let source = i64::try_from(source)?;
        source
            .try_into()
            .map_err(|_| ValueError::IncorrectParameterType)
    }
}

impl TryParamConvertFromValue for usize {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        let source = i64::try_from(source)?;
        source
            .try_into()
            .map_err(|_| ValueError::IncorrectParameterType)
    }
}

/// Starlark `None` or another value.
pub enum EitherValueOrNone<T> {
    None,
    NotNone(T),
}

impl<T: TryParamConvertFromValue> TryParamConvertFromValue for EitherValueOrNone<T> {
    fn try_from(source: Value) -> Result<Self, ValueError> {
        if source.get_type() == "NoneType" {
            Ok(EitherValueOrNone::None)
        } else {
            Ok(EitherValueOrNone::NotNone(T::try_from(source)?))
        }
    }
}

#[cfg(test)]
mod test {
    use crate::gc;
    use crate::starlark_fun;
    use crate::starlark_module;
    use crate::starlark_parse_param_type;
    use crate::starlark_signature;
    use crate::starlark_signature_extraction;
    use crate::starlark_signatures;

    use crate::eval::noload::eval;
    use crate::stdlib::global_environment;
    use crate::syntax::dialect::Dialect;
    use crate::values::Value;
    use codemap::CodeMap;
    use std::sync::{Arc, Mutex};

    starlark_module! { global =>
        cc_binary(name: String, srcs: Vec<String> = Vec::new()) {
            // real implementation may write it to a global variable
            Ok(Value::new(format!("{:?} {:?}", name, srcs)))
        }
    }

    #[test]
    fn test_simple() {
        let (mut env, mut type_values) = global_environment();
        global(&mut env, &mut type_values);

        let mut child = env.child("my");
        let _g = gc::push_env(&child);

        let r = eval(
            &Arc::new(Mutex::new(CodeMap::new())),
            "test_simple.star",
            "cc_binary(name='star', srcs=['a.cc', 'b.cc'])",
            Dialect::Build,
            &mut child,
            &type_values,
        )
        .unwrap();

        assert_eq!(r#""star" ["a.cc", "b.cc"]"#, r.to_str());
    }
}
