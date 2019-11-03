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

//! Implementation of `inspect` builtin.

use crate::values::Value;

starlark_module! { global =>
    /// Return some internals about the value.
    ///
    /// This function is to be used for debugging only, it's format is not specified,
    /// and may change any time.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default("
    /// a = []
    /// 'List' in inspect(a).rust_type_name
    /// # ").unwrap());
    /// ```
    inspect(value, /) {
        Ok(Value::new(value.inspect()))
    }
}

#[cfg(test)]
mod test {
    use crate::eval::noload;
    use crate::stdlib::global_environment_for_repl_and_tests;
    use crate::syntax::dialect::Dialect;
    use crate::values::Immutable;
    use crate::values::TypedValue;
    use crate::values::Value;
    use std::iter;

    #[test]
    fn inspect() {
        struct TestInspectable {}

        impl TypedValue for TestInspectable {
            type Holder = Immutable<Self>;
            const TYPE: &'static str = "test_inspectable";

            fn values_for_descendant_check_and_freeze<'a>(
                &'a self,
            ) -> Box<dyn Iterator<Item = Value>> {
                Box::new(iter::empty())
            }

            fn inspect_custom(&self) -> Value {
                Value::from("test test")
            }
        }

        let (mut env, type_values) = global_environment_for_repl_and_tests();
        env.set("ti", Value::new(TestInspectable {})).unwrap();
        let custom = noload::eval(
            &Default::default(),
            "test.sky",
            "inspect(ti).custom",
            Dialect::Bzl,
            &mut env,
            &type_values,
        )
        .unwrap();
        assert_eq!(
            "test test",
            custom.downcast_ref::<String>().unwrap().as_str()
        );
    }
}
