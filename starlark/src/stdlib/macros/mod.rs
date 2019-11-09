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

//! Define the `starlark_module!` macro to reduce written boilerplate when adding
//! native functions to starlark.

use crate::environment::TypeValues;
use crate::eval::call_stack::CallStack;
use crate::values::cell::ObjectRef;
use crate::values::cell::ObjectRefMut;
use crate::values::error::ValueError;
use crate::values::function::ParameterParser;
use crate::values::Mutable;
use crate::values::TypedValue;
use crate::values::Value;

pub mod param;
pub mod signature;

#[doc(hidden)]
#[macro_export]
macro_rules! starlark_signature {
    ($signature:ident) => {};
    ($signature:ident / $(,$($rest:tt)+)?) => {
        $signature.push_slash();
        $( starlark_signature!($signature $($rest)+) )?
    };
    ($signature:ident call_stack $e:ident $(,$($rest:tt)+)?) => {
        $( starlark_signature!($signature $($rest)+) )?;
    };
    ($signature:ident env $e:ident $(,$($rest:tt)+)?) => {
        $( starlark_signature!($signature $($rest)+) )?;
    };
    ($signature:ident * $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        $signature.push_args(stringify!($t));
        $( starlark_signature!($signature $($rest)+) )?
    };
    ($signature:ident ** $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        $signature.push_kwargs(stringify!($t));
        $( starlark_signature!($signature $($rest)+) )?
    };

    // handle params without default value (both named and unnamed)
    ($signature:ident $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        $signature.push_normal(stringify!($t));
        $( starlark_signature!($signature $($rest)+) )?
    };
    ($signature:ident ? $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        $signature.push_optional(stringify!($t));
        $( starlark_signature!($signature $($rest)+) )?
    };

    // Remove `&mut` and `&` from type because default value type should be inferred
    // without `&`, e. g. in this parameter description "zzzz" should be converted
    // to `String` not to `&String`:
    // ```
    // foo: &String = "zzzz"
    // ```
    ($signature:ident $t:ident : & mut $($rest:tt)+) => {
        starlark_signature!($signature $t : $($rest)+)
    };
    ($signature:ident $t:ident : & $($rest:tt)+) => {
        starlark_signature!($signature $t : $($rest)+)
    };

    // handle params with default value (both named and unnamed)
    ($signature:ident $t:ident : $pt:ty = $e:expr $(,$($rest:tt)+)?) => {
        // explicitly specify parameter type to:
        // * verify that default value is convertible to required type
        // * help type inference find type parameters
        $signature.push_with_default_value::<starlark_parse_param_type!(1 : $pt)>(
            stringify!($t),
            $e,
        );
        $( starlark_signature!($signature $($rest)+) )?
    };
    ($signature:ident $t:ident = $e:expr $(,$($rest:tt)+)?) => {
        $signature.push_with_default_value(
            stringify!($t),
            $e,
        );
        $( starlark_signature!($signature $($rest)+) )?
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! starlark_parse_param_type {
    (1 : $pt:ty) => { $pt };
    (? : $pt:ty) => { $pt };
    (* : $pt:ty) => { $pt };
    (** : $pt:ty) => { $pt };
    (1) => {
        $crate::values::Value
    };
    (?) => {
        ::std::option::Option<$crate::values::Value>
    };
    (*) => {
        ::std::vec::Vec<$crate::values::Value>
    };
    (**) => {
        ::linked_hash_map::LinkedHashMap<::std::string::String, $crate::values::Value>
    };
}

/// Structure used to simplify passing several arguments through
/// `starlark_signature_extraction` macro.
#[doc(hidden)]
pub struct SignatureExtractionContext<'a> {
    pub call_stack: &'a mut CallStack,
    pub env: &'a TypeValues,
    pub args: ParameterParser<'a>,
}

/// Value operations used in macros
#[doc(hidden)]
impl Value {
    /// `downcast_mut` shortcut used in macros.
    pub fn downcast_mut_param<T: TypedValue<Holder = Mutable<T>>>(
        &self,
        param: &'static str,
    ) -> Result<ObjectRefMut<'_, T>, ValueError> {
        match self.downcast_mut()? {
            Some(v) => Ok(v),
            None => Err(ValueError::IncorrectParameterTypeNamed(param)),
        }
    }

    /// `downcast_ref` shortcut used in macros.
    pub fn downcast_ref_param<T: TypedValue>(
        &self,
        param: &'static str,
    ) -> Result<ObjectRef<'_, T>, ValueError> {
        match self.downcast_ref() {
            Some(v) => Ok(v),
            None => Err(ValueError::IncorrectParameterTypeNamed(param)),
        }
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! starlark_signature_extraction {
    ($ctx:ident) => {};
    ($ctx:ident / $(,$($rest:tt)+)?) => {
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };
    ($ctx:ident call_stack $e:ident $(,$($rest:tt)+)?) => {
        let $e = $ctx.call_stack;
        $( starlark_signature_extraction!($ctx $($rest)+) )?;
    };
    ($ctx:ident env $e:ident $(,$($rest:tt)+)?) => {
        let $e = $ctx.env;
        $( starlark_signature_extraction!($ctx $($rest)+) )?;
    };
    ($ctx:ident * $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        #[allow(unused_mut)]
        let mut $t: starlark_parse_param_type!(* $(: $pt)?) =
            $ctx.args.next_arg()?.into_args_array(stringify!($t))?;
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };
    ($ctx:ident ** $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        #[allow(unused_mut)]
        let mut $t: starlark_parse_param_type!(** $(: $pt)?) =
            $ctx.args.next_arg()?.into_kw_args_dict(stringify!($t))?;
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };

    ($ctx:ident ? $t:ident $(: $pt:ty)? $(,$($rest:tt)+)?) => {
        #[allow(unused_mut)]
        let mut $t: starlark_parse_param_type!(? $(: $pt)?) =
            $ctx.args.next_arg()?.into_optional(stringify!($t))?;
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };

    // Downcast argument to requested type.
    // Note here we explicitly match `&` and `&mut` literals here,
    // and this macro branch must come before the `: $pt:ty` match,
    // because `&mut T` can be successfully matched as `$pt:ty`.

    ($ctx:ident $t:ident : &mut $pt:ty $(= $e:expr)? $(,$($rest:tt)+)?) => {
        let v: $crate::values::Value = $ctx.args.next_arg()?.into_normal(stringify!($t))?;
        let mut r: $crate::values::cell::ObjectRefMut<$pt> = v.downcast_mut_param(stringify!($t))?;
        #[allow(unused_mut)]
        let mut $t: &mut $pt = &mut *r;
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };
    ($ctx:ident $t:ident : &$pt:ty $(= $e:expr)? $(,$($rest:tt)+)?) => {
        let v: $crate::values::Value = $ctx.args.next_arg()?.into_normal(stringify!($t))?;
        let r: $crate::values::cell::ObjectRef<$pt> = v.downcast_ref_param(stringify!($t))?;
        let $t: &$pt = &*r;
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };

    ($ctx:ident $t:ident $(: $pt:ty)? $(= $e:expr)? $(,$($rest:tt)+)?) => {
        #[allow(unused_mut)]
        let mut $t: starlark_parse_param_type!(1 $(: $pt)?) =
            $ctx.args.next_arg()?.into_normal(stringify!($t))?;
        $( starlark_signature_extraction!($ctx $($rest)+) )?
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! starlark_fun {
    ($(#[$attr:meta])* $fn:ident ( $($signature:tt)* ) { $($content:tt)* } $($($rest:tt)+)?) => {
        $(#[$attr])*
        fn $fn(
            call_stack: &mut $crate::eval::call_stack::CallStack,
            env: &$crate::environment::TypeValues,
            args: $crate::values::function::ParameterParser,
        ) -> $crate::values::ValueResult {
            let mut ctx = $crate::stdlib::macros::SignatureExtractionContext {
                call_stack,
                env,
                args,
            };
            starlark_signature_extraction!(ctx $($signature)*);
            ctx.args.check_no_more_args()?;
            $($content)*
        }
        $(starlark_fun! {
            $($rest)+
        })?
    };
    ($(#[$attr:meta])* $ty:ident . $fn:ident ( $($signature:tt)* ) { $($content:tt)* }
            $($($rest:tt)+)?) => {
        $(#[$attr])*
        fn $fn(
            call_stack: &mut $crate::eval::call_stack::CallStack,
            env: &$crate::environment::TypeValues,
            args: $crate::values::function::ParameterParser,
        ) -> $crate::values::ValueResult {
            let mut ctx = $crate::stdlib::macros::SignatureExtractionContext {
                call_stack,
                env,
                args,
            };
            starlark_signature_extraction!(ctx $($signature)*);
            ctx.args.check_no_more_args()?;
            $($content)*
        }
        $(starlark_fun! {
            $($rest)+
        })?
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! starlark_signatures {
    ($env:expr, $type_values:expr, $(#[$attr:meta])* $name:ident ( $($signature:tt)* ) { $($content:tt)* }
            $($($rest:tt)+)?) => {
        {
            let name = stringify!($name).trim_matches('_');
            #[allow(unused_mut)]
            let mut signature = $crate::stdlib::macros::signature::SignatureBuilder::default();
            starlark_signature!(signature $($signature)*);
            $env.set(name, $crate::values::function::NativeFunction::new(name.to_owned(), $name, signature.build())).unwrap();
        }
        $(starlark_signatures!{ $env, $type_values,
            $($rest)+
        })?
    };
    ($env:expr, $type_values:expr, $(#[$attr:meta])* $ty:ident . $name:ident ( $($signature:tt)* ) { $($content:tt)* }
            $($($rest:tt)+)?) => {
        {
            let name = stringify!($name).trim_matches('_');
            let mut signature = $crate::stdlib::macros::signature::SignatureBuilder::default();
            starlark_signature!(signature $($signature)*);
            $type_values.add_type_value(stringify!($ty), name,
                $crate::values::function::NativeFunction::new(name.to_owned(), $name, signature.build()));
        }
        $(starlark_signatures!{ $env, $type_values,
            $($rest)+
        })?
    }
}

/// Declare a starlark module that store one or several function
///
/// To declare a module with name `name`, the macro would be called:
///
/// ```rust,ignore
/// starlark_module!{ name =>
///    // Starlark function definition goes there
/// }
/// ```
///
/// For instance, the following example would declare two functions `str`, `my_fun` and `dbg` in a
/// module named `my_starlark_module`:
///
/// ```rust
/// # #[macro_use] extern crate starlark;
/// # use starlark::values::*;
/// # use starlark::values::none::NoneType;
/// # use starlark::environment::Environment;
/// # use starlark::environment::TypeValues;
/// starlark_module!{ my_starlark_module =>
///     // Declare a 'str' function (_ are trimmed away and just here to avoid collision with
///     // reserved keyword)
///     // `a` argument will be binded to a `a` Rust value, the `/` marks all preceding arguments
///     // as positional only.
///     __str__(a, /) {
///       Ok(Value::new(a.to_str().to_owned()))
///     }
///
///     // Declare a function my_fun that takes one positional parameter 'a', a named and
///     // positional parameter 'b', a args array 'args' and a keyword dictionary `kwargs`
///     my_fun(a, /, b, c = 1, *args, **kwargs) {
///       // ...
/// # Ok(Value::new(true))
///     }
///
///     // Functions can optionally downcast parameter to `TypedValue` type
///     // adding `&` or `&mut` after colon.
///     // Note downcasting only works for types directly stored in `Value`,
///     // which are `TypedValue` types, e. g.
///     hello(person: &String) {
///         Ok(Value::from(format!("Hello {}!", person)))
///     }
///
///     // Functions can also optionally specify parameter conversion after colon.
///     // Parameter can be any type which implements `TryParamConvertFromValue`.
///     // When parameter type is not specified, it is defaulted to `Value`
///     // for regular parameters, `Vec<Value>` for `*args`
///     // and `LinkedHashMap<String, Value>` for `**kwargs`.
///     avg(vs: Vec<i64>) {
///         // ...
/// # Ok(Value::new(NoneType::None))
///     }
///
///     // It is also possible to capture the call stack with
///     // `call_stack name` (type `Vec<String>`). For example a `dbg` function that print the
///     // the call stack:
///     dbg(call_stack cs) {
///        println!(
///            "In:{}",
///            cs.print_with_newline_before()
///        );
///        Ok(Value::from(NoneType::None))
///     }
/// }
/// #
/// # fn main() {
/// #    let mut env = Environment::new("test");
/// #    let mut type_values = TypeValues::default();
/// #    my_starlark_module(&mut env, &mut type_values);
/// #    assert_eq!(env.get("str").unwrap().get_type(), "function");
/// #    assert_eq!(env.get("my_fun").unwrap().get_type(), "function");
/// #    assert_eq!(env.get("hello").unwrap().get_type(), "function");
/// #    assert_eq!(env.get("avg").unwrap().get_type(), "function");
/// # }
/// ```
///
/// The module would declare a function `my_starlark_module` that can be called to add the
/// corresponding functions to an environment.
///
/// ```
/// # #[macro_use] extern crate starlark;
/// # use starlark::values::*;
/// # use starlark::environment::Environment;
/// # use starlark::environment::TypeValues;
/// # starlark_module!{ my_starlark_module =>
/// #     __str__(a, /) { Ok(Value::new(a.to_str().to_owned())) }
/// #     my_fun(a, /, b, c = 1, *args, **kwargs) { Ok(Value::new(true)) }
/// # }
/// # fn main() {
/// #    let mut env = Environment::new("test");
/// #    let mut type_values = TypeValues::default();
/// #    my_starlark_module(&mut env, &mut type_values);
/// #    assert_eq!(env.get("str").unwrap().get_type(), "function");
/// #    assert_eq!(env.get("my_fun").unwrap().get_type(), "function");
/// # }
/// ```
///
/// Additionally function might be declared for a type by prefixing them by `type.`, e.g the
/// definition of a `hello` function for the `string` type would look like:
///
/// ```rust
/// # #[macro_use] extern crate starlark;
/// # use starlark::values::*;
/// # use starlark::environment::Environment;
/// # use starlark::environment::TypeValues;
/// starlark_module!{ my_starlark_module =>
///     // The first argument is always self in that module but we use "this" because "self" is a
///     // a rust keyword.
///     string.hello(this) {
///        Ok(Value::new(
///            format!("Hello, {}", this.to_str())
///        ))
///     }
/// }
/// #
/// # fn main() {
/// #    let mut env = Environment::new("test");
/// #    let mut type_values = TypeValues::default();
/// #    my_starlark_module(&mut env, &mut type_values);
/// #    assert_eq!(type_values.get_type_value(&Value::from(""), "hello").unwrap().get_type(), "function");
/// # }
/// ```
#[macro_export]
macro_rules! starlark_module {
    ($name:ident => $($t:tt)*) => (
        starlark_fun!{
            $($t)*
        }

        #[doc(hidden)]
        pub fn $name(env: &mut $crate::environment::Environment, type_values: &mut $crate::environment::TypeValues) {
            starlark_signatures!{ env, type_values,
                $($t)*
            }
            let _ = (env, type_values);
        }
    )
}

/// Shortcut for returning an error from the code, message and label.
///
/// # Parameters:
///
/// * $code is a short code to uniquely identify the error.
/// * $message is the long explanation for the user of the error.
/// * $label is a a short description of the error to be put next to the code.
#[macro_export]
macro_rules! starlark_err {
    ($code:expr, $message:expr, $label:expr) => {
        return Err($crate::values::error::RuntimeError {
            code: $code,
            message: $message,
            label: $label,
        }
        .into());
    };
}

/// A shortcut to assert the type of a value
///
/// # Parameters:
///
/// * $e the value to check type for.
/// * $fn the function name (&'static str).
/// * $ty the expected type (ident)
#[macro_export]
macro_rules! check_type {
    ($e:ident, $fn:expr, $ty:ident) => {
        if $e.get_type() != stringify!($ty) {
            starlark_err!(
                INCORRECT_PARAMETER_TYPE_ERROR_CODE,
                format!(
                    concat!(
                        $fn,
                        "() expect a ",
                        stringify!($ty),
                        " as first parameter while got a value of type {}."
                    ),
                    $e.get_type()
                ),
                format!(
                    concat!("type {} while expected ", stringify!($ty)),
                    $e.get_type()
                )
            )
        }
    };
}

/// Convert 2 indices according to Starlark indices convertion for function like .index.
///
/// # Parameters:
///
/// * $this: the identifier of self object
/// * $start: the variable denoting the start index
/// * $end: the variable denoting the end index (optional)
#[macro_export]
macro_rules! convert_indices {
    ($this:ident, $start:ident, $end:ident) => {
        let len = $this.length()?;
        let $end = if $end.get_type() == "NoneType" {
            len
        } else {
            $end.to_int()?
        };
        let $start = if $start.get_type() == "NoneType" {
            0
        } else {
            $start.to_int()?
        };
        let $end = if $end < 0 { $end + len } else { $end };
        let $start = if $start < 0 { $start + len } else { $start };
        let $end = if $end < 0 {
            0
        } else {
            if $end > len {
                len as usize
            } else {
                $end as usize
            }
        };
        let $start = if $start < 0 {
            0
        } else {
            if $start > len {
                len as usize
            } else {
                $start as usize
            }
        };
    };
    ($this:ident, $start:ident) => {
        let len = $this.length()?;
        let $start = if $start.get_type() == "NoneType" {
            0
        } else {
            $start.to_int()?
        };
        let $start = if $start < 0 { $start + len } else { $start };
        let $start = if $start < 0 {
            0
        } else {
            if $start > len {
                len as usize
            } else {
                $start as usize
            }
        };
    };
}

#[cfg(test)]
mod tests {
    use crate::environment::Environment;
    use crate::environment::TypeValues;
    use crate::values::none::NoneType;
    use crate::values::Value;

    #[test]
    fn no_arg() {
        starlark_module! { global =>
            nop() {
                Ok(Value::new(NoneType::None))
            }
        }

        let mut env = Environment::new("root");
        global(&mut env, &mut TypeValues::default());
        env.get("nop").unwrap();
    }
}
