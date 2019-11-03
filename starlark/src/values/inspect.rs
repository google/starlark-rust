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

//! Utility for easier implementation of `inspect`.

use crate::values::dict::Dictionary;
use crate::values::none::NoneType;
use crate::values::Value;
use codemap::Spanned;
use std::collections::HashMap;

/// Convert "inspectable" to a Starlark value.
///
/// Somewhat similar to `Value::from`, but also works with other types
/// which are not supposed to converted to `Value` implicitly.
pub(crate) trait Inspectable {
    fn inspect(&self) -> Value;
}

impl<A: Inspectable> Inspectable for &'_ A {
    fn inspect(&self) -> Value {
        (**self).inspect()
    }
}

impl Inspectable for usize {
    fn inspect(&self) -> Value {
        Value::from(*self)
    }
}

impl Inspectable for String {
    fn inspect(&self) -> Value {
        Value::from(self.as_str())
    }
}

impl<A: Inspectable> Inspectable for Box<A> {
    fn inspect(&self) -> Value {
        (**self).inspect()
    }
}

impl<A: Inspectable> Inspectable for Option<A> {
    fn inspect(&self) -> Value {
        match self {
            None => Value::new(NoneType::None),
            Some(v) => (v.inspect(),).into(),
        }
    }
}

impl<V: Inspectable> Inspectable for Vec<V> {
    fn inspect(&self) -> Value {
        Value::from(self.iter().map(V::inspect).collect::<Vec<_>>())
    }
}

impl<A: Inspectable, B: Inspectable> Inspectable for (A, B) {
    fn inspect(&self) -> Value {
        Value::from((self.0.inspect(), self.1.inspect()))
    }
}

impl<A: Inspectable, B: Inspectable, C: Inspectable> Inspectable for (A, B, C) {
    fn inspect(&self) -> Value {
        Value::from((self.0.inspect(), self.1.inspect(), self.2.inspect()))
    }
}

impl<A: Inspectable, B: Inspectable, C: Inspectable, D: Inspectable> Inspectable for (A, B, C, D) {
    fn inspect(&self) -> Value {
        Value::from((
            self.0.inspect(),
            self.1.inspect(),
            self.2.inspect(),
            self.3.inspect(),
        ))
    }
}

impl<A: Inspectable, B: Inspectable, C: Inspectable, D: Inspectable, E: Inspectable> Inspectable
    for (A, B, C, D, E)
{
    fn inspect(&self) -> Value {
        Value::from((
            self.0.inspect(),
            self.1.inspect(),
            self.2.inspect(),
            self.3.inspect(),
            self.4.inspect(),
        ))
    }
}

impl<K: Inspectable, V: Inspectable> Inspectable for HashMap<K, V> {
    fn inspect(&self) -> Value {
        let mut map = Dictionary::new_typed();
        for (k, v) in self {
            map.insert(k.inspect(), v.inspect()).unwrap();
        }
        Value::new(map)
    }
}

impl<A: Inspectable> Inspectable for Spanned<A> {
    fn inspect(&self) -> Value {
        self.node.inspect()
    }
}
