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

//! Define the int type for Starlark.

use crate::values::error::UnsupportedOperation;
use crate::values::error::ValueError;
use crate::values::frozen::FrozenOnCreation;
use crate::values::*;
use std::cmp::Ordering;
use std::fmt;
use std::iter;

// A convenient macro for testing and documentation.
#[macro_export]
#[doc(hidden)]
macro_rules! int_op {
    ($v1:tt. $op:ident($v2:expr)) => {
        $crate::values::Value::new($v1)
            .$op($crate::values::Value::new($v2))
            .unwrap()
            .to_int()
            .unwrap()
    };
    ($v1:tt. $op:ident()) => {
        $crate::values::Value::new($v1)
            .$op()
            .unwrap()
            .to_int()
            .unwrap()
    };
}

macro_rules! from_int {
    ($x: ty, $y: tt) => {
        impl From<$x> for Value {
            fn from(a: $x) -> Value {
                Value::new(a as $y)
            }
        }
    };
}

from_int!(i8, i64);
from_int!(i16, i64);
from_int!(i32, i64);
from_int!(u8, i64);
from_int!(u16, i64);
from_int!(u32, i64);
// TODO: check for overflow
from_int!(u64, i64);
// TODO: check for overflow
from_int!(usize, i64);
from_int!(isize, i64);

impl From<i64> for Value {
    fn from(v: i64) -> Self {
        Value::new(v)
    }
}

fn i64_arith_bin_op<F>(left: i64, right: Value, op: UnsupportedOperation, f: F) -> ValueResult
where
    F: FnOnce(i64, i64) -> Result<i64, ValueError>,
{
    match right.downcast_ref::<i64>() {
        Some(right) => Ok(Value::new(f(left, *right)?)),
        None => Err(ValueError::OperationNotSupported {
            op,
            left: i64::TYPE.to_owned(),
            right: Some(right.get_type().to_owned()),
        }),
    }
}

/// Define the int type
impl TypedValue for i64 {
    type Holder = Immutable<Self>;
    const TYPE: &'static str = "int";

    const INLINE: bool = true;

    fn new_value(self) -> Value {
        Value(ValueInner::Int(self))
    }

    fn equals(&self, other: &i64) -> Result<bool, ValueError> {
        Ok(self == other)
    }
    fn to_str_impl(&self, buf: &mut String) -> fmt::Result {
        write!(buf, "{}", self)
    }
    fn to_repr_impl(&self, buf: &mut String) -> fmt::Result {
        write!(buf, "{}", self)
    }
    fn to_int(&self) -> Result<i64, ValueError> {
        Ok(*self)
    }
    fn to_bool(&self) -> bool {
        *self != 0
    }
    fn get_hash(&self) -> Result<u64, ValueError> {
        Ok(*self as u64)
    }
    fn plus(&self) -> Result<i64, ValueError> {
        Ok(*self)
    }
    fn minus(&self) -> Result<i64, ValueError> {
        self.checked_neg().ok_or(ValueError::IntegerOverflow)
    }
    fn add(&self, other: &i64) -> Result<i64, ValueError> {
        self.checked_add(*other).ok_or(ValueError::IntegerOverflow)
    }
    fn sub(&self, other: &i64) -> Result<i64, ValueError> {
        self.checked_sub(*other).ok_or(ValueError::IntegerOverflow)
    }
    fn mul(&self, other: Value) -> ValueResult {
        match other.downcast_ref::<i64>() {
            Some(other) => self
                .checked_mul(*other)
                .ok_or(ValueError::IntegerOverflow)
                .map(Value::new),
            None => other.mul(Value::new(*self)),
        }
    }
    fn percent(&self, other: Value) -> ValueResult {
        i64_arith_bin_op(*self, other, UnsupportedOperation::Percent, |a, b| {
            if b == 0 {
                return Err(ValueError::DivisionByZero);
            }
            // In Rust `i64::min_value() % -1` is overflow, but we should eval it to zero.
            if *self == i64::min_value() && b == -1 {
                return Ok(0);
            }
            let r = a % b;
            if r == 0 {
                Ok(0)
            } else {
                Ok(if b.signum() != r.signum() { r + b } else { r })
            }
        })
    }
    fn div(&self, other: Value) -> ValueResult {
        self.floor_div(other)
    }
    fn floor_div(&self, other: Value) -> ValueResult {
        i64_arith_bin_op(*self, other, UnsupportedOperation::FloorDiv, |a, b| {
            if b == 0 {
                return Err(ValueError::DivisionByZero);
            }
            let sig = b.signum() * a.signum();
            let offset = if sig < 0 && a % b != 0 { 1 } else { 0 };
            match a.checked_div(b) {
                Some(div) => Ok(div - offset),
                None => Err(ValueError::IntegerOverflow),
            }
        })
    }

    fn values_for_descendant_check_and_freeze<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = Value> + 'a> {
        Box::new(iter::empty())
    }

    fn compare(&self, other: &i64) -> Result<Ordering, ValueError> {
        Ok(self.cmp(other))
    }
}

impl FrozenOnCreation for i64 {}

#[cfg(test)]
mod test {
    use crate::int_op;

    #[test]
    fn test_arithmetic_operators() {
        assert_eq!(1, int_op!(1.plus())); // 1.plus() = +1 = 1
        assert_eq!(-1, int_op!(1.minus())); // 1.minus() = -1
        assert_eq!(3, int_op!(1.add(2))); // 1.add(2) = 1 + 2 = 3
        assert_eq!(-1, int_op!(1.sub(2))); // 1.sub(2) = 1 - 2 = -1
        assert_eq!(6, int_op!(2.mul(3))); // 2.mul(3) = 2 * 3 = 6
                                          // Remainder of the floored division: 5.percent(3) = 5 % 3 = 2
        assert_eq!(2, int_op!(5.percent(3)));
        assert_eq!(3, int_op!(7.div(2))); // 7.div(2) = 7 / 2 = 3
    }
}
