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

//! `range()` builtin implementation

use crate::values::iter::TypedIterable;
use crate::values::{Immutable, TypedValue, Value, ValueError};
use std::num::NonZeroI64;
use std::{iter, mem};

/// Representation of `range()` type.
#[derive(Clone, Debug)]
pub struct Range {
    start: i64,
    stop: i64,
    step: NonZeroI64,
}

impl Range {
    pub fn new(start: i64, stop: i64, step: NonZeroI64) -> Range {
        Range { start, stop, step }
    }
}

/// Implementation of iterator over range.
struct RangeIterator(Range);

impl Iterator for RangeIterator {
    type Item = Value;

    fn next(&mut self) -> Option<Value> {
        if !self.0.to_bool() {
            return None;
        }

        let new_start = self.0.start.saturating_add(self.0.step.get());
        Some(Value::new(mem::replace(&mut self.0.start, new_start)))
    }
}

impl TypedValue for Range {
    const TYPE: &'static str = "range";

    fn to_str(&self) -> String {
        self.to_repr()
    }

    fn to_repr(&self) -> String {
        if self.step.get() != 1 {
            format!("range({}, {}, {})", self.start, self.stop, self.step)
        } else if self.start != 0 {
            format!("range({}, {})", self.start, self.stop)
        } else {
            format!("range({})", self.stop)
        }
    }

    fn to_bool(&self) -> bool {
        (self.start < self.stop && self.step.get() > 0)
            || (self.start > self.stop && self.step.get() < 0)
    }

    fn length(&self) -> Result<i64, ValueError> {
        if self.start == self.stop {
            return Ok(0);
        }

        // If step is into opposite direction of stop, then length is zero.
        if (self.stop >= self.start) != (self.step.get() > 0) {
            return Ok(0);
        }

        // Convert range and step to `u64`
        let (dist, step) = if self.step.get() >= 0 {
            (
                self.stop.wrapping_sub(self.start) as u64,
                self.step.get() as u64,
            )
        } else {
            (
                self.start.wrapping_sub(self.stop) as u64,
                self.step.get().wrapping_neg() as u64,
            )
        };
        let i = ((dist - 1) / step + 1) as i64;
        if i >= 0 {
            Ok(i)
        } else {
            Err(ValueError::IntegerOverflow)
        }
    }

    fn at(&self, index: Value) -> Result<Value, ValueError> {
        let index = index.convert_index(self.length()?)?;
        // Must not overflow if `length` is computed correctly
        Ok(Value::new(self.start + self.step.get() * index))
    }

    fn equals(&self, other: &Range) -> Result<bool, ValueError> {
        let self_length = self.length()?;
        let other_length = other.length()?;
        if self_length == 0 || other_length == 0 {
            return Ok(self_length == other_length);
        }
        if self.start != other.start {
            return Ok(false);
        }
        if self_length == 1 || other_length == 1 {
            return Ok(self_length == other_length);
        }
        debug_assert!(self_length > 1);
        debug_assert!(other_length > 1);
        if self.step.get() == other.step.get() {
            return Ok(self_length == other_length);
        } else {
            return Ok(false);
        }
    }

    fn slice(
        &self,
        start: Option<Value>,
        stop: Option<Value>,
        stride: Option<Value>,
    ) -> Result<Value, ValueError> {
        let (start, stop, step) =
            Value::convert_slice_indices(self.length()?, start, stop, stride)?;
        return Ok(Value::new(Range {
            start: self
                .start
                .checked_add(
                    start
                        .checked_mul(self.step.get())
                        .ok_or(ValueError::IntegerOverflow)?,
                )
                .ok_or(ValueError::IntegerOverflow)?,
            stop: self
                .start
                .checked_add(
                    stop.checked_mul(self.step.get())
                        .ok_or(ValueError::IntegerOverflow)?,
                )
                .ok_or(ValueError::IntegerOverflow)?,
            step: NonZeroI64::new(
                step.checked_mul(self.step.get())
                    .ok_or(ValueError::IntegerOverflow)?,
            )
            .unwrap(),
        }));
    }

    fn iter(&self) -> Result<&dyn TypedIterable, ValueError> {
        Ok(self)
    }

    fn is_in(&self, other: &Value) -> Result<bool, ValueError> {
        let other = match other.downcast_ref::<i64>() {
            Some(other) => *other,
            None => {
                // Go implementation errors here,
                // Python3 returns `False`.
                // ```
                // "a" in range(3)
                // ```
                return Ok(false);
            }
        };
        if !self.to_bool() {
            return Ok(false);
        }
        if self.start == other {
            return Ok(true);
        }
        if self.step.get() > 0 {
            if other < self.start || other >= self.stop {
                return Ok(false);
            }
            Ok((other.wrapping_sub(self.start) as u64) % (self.step.get() as u64) == 0)
        } else {
            if other > self.start || other <= self.stop {
                return Ok(false);
            }
            Ok(
                (self.start.wrapping_sub(other) as u64) % (self.step.get().wrapping_neg() as u64)
                    == 0,
            )
        }
    }

    type Holder = Immutable<Range>;

    fn values_for_descendant_check_and_freeze(&self) -> Box<dyn Iterator<Item = Value>> {
        Box::new(iter::empty())
    }
}

/// For tests
impl PartialEq for Range {
    fn eq(&self, other: &Range) -> bool {
        self.equals(other).unwrap()
    }
}

impl TypedIterable for Range {
    fn to_iter(&self) -> Box<dyn Iterator<Item = Value>> {
        Box::new(RangeIterator(self.clone()))
    }
}

#[cfg(test)]
mod test {
    use crate::values::range::Range;
    use crate::values::{TypedValue, ValueError};
    use std::i64;
    use std::num::NonZeroI64;

    fn range(start: i64, stop: i64, range: i64) -> Range {
        Range {
            start,
            stop,
            step: NonZeroI64::new(range).unwrap(),
        }
    }

    fn range_start_stop(start: i64, stop: i64) -> Range {
        range(start, stop, 1)
    }

    fn range_stop(stop: i64) -> Range {
        range_start_stop(0, stop)
    }

    #[test]
    fn length_stop() {
        assert_eq!(Ok(0), range_stop(0).length());
        assert_eq!(Ok(17), range_stop(17).length());
    }

    #[test]
    fn length_start_stop() {
        assert_eq!(Ok(20), range_start_stop(10, 30).length());
        assert_eq!(Ok(0), range_start_stop(10, -30).length());
        assert_eq!(
            Ok(i64::max_value()),
            range_start_stop(0, i64::max_value()).length()
        );
        assert_eq!(
            Err(ValueError::IntegerOverflow),
            range_start_stop(-1, i64::max_value()).length()
        );
    }

    #[test]
    fn length_start_stop_step() {
        assert_eq!(Ok(5), range(0, 10, 2).length());
        assert_eq!(Ok(5), range(0, 9, 2).length());
        assert_eq!(Ok(0), range(0, 10, -2).length());
        assert_eq!(Ok(5), range(10, 0, -2).length());
        assert_eq!(Ok(5), range(9, 0, -2).length());
        assert_eq!(Ok(1), range(4, 14, 10).length());
    }

    #[test]
    fn eq() {
        assert_eq!(range_stop(0), range(2, 1, 3));
    }
}
