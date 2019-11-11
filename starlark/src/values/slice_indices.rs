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

//! Slice indices utils live here.

use crate::values::error::ValueError;
use crate::values::Value;

impl Value {
    /// Macro to parse the index for at/set_at methods.
    ///
    /// Return an `i64` from self corresponding to the index recenterd between 0 and len.
    /// Raise the correct errors if the value is not numeric or the index is out of bound.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use starlark::values::*;
    /// # assert!(
    /// Value::new(6).convert_index(7).unwrap() == 6
    /// # );
    /// # assert!(
    /// Value::new(-1).convert_index(7).unwrap() == 6
    /// # );
    /// ```
    ///
    /// The following examples would return an error
    /// ```rust
    /// # use starlark::values::*;
    /// # use starlark::values::error::*;
    /// # use starlark::values::string;
    /// # assert!(
    /// Value::from("a").convert_index(7) == Err(ValueError::IncorrectParameterType)
    /// # );
    /// # assert!(
    /// Value::new(8).convert_index(7) == Err(ValueError::IndexOutOfBound(8))   // 8 > 7 = len
    /// # );
    /// # assert!(
    /// Value::new(-8).convert_index(7) == Err(ValueError::IndexOutOfBound(-1)) // -8 + 7 = -1 < 0
    /// # );
    /// ```
    pub fn convert_index(&self, len: i64) -> Result<i64, ValueError> {
        match self.value_holder().to_int_dyn() {
            Ok(x) => {
                let i = if x < 0 {
                    len.checked_add(x).ok_or(ValueError::IntegerOverflow)?
                } else {
                    x
                };
                if i < 0 || i >= len {
                    Err(ValueError::IndexOutOfBound(i))
                } else {
                    Ok(i)
                }
            }
            Err(..) => Err(ValueError::IncorrectParameterType),
        }
    }
}

// To be called by convert_slice_indices only
fn convert_index_aux(
    len: i64,
    v1: Option<Value>,
    default: i64,
    min: i64,
    max: i64,
) -> Result<i64, ValueError> {
    if let Some(v) = v1 {
        if v.get_type() == "NoneType" {
            Ok(default)
        } else {
            match v.to_int() {
                Ok(x) => {
                    let i = if x < 0 { len + x } else { x };
                    if i < min {
                        Ok(min)
                    } else if i > max {
                        Ok(max)
                    } else {
                        Ok(i)
                    }
                }
                Err(..) => Err(ValueError::IncorrectParameterType),
            }
        }
    } else {
        Ok(default)
    }
}

/// Parse indices for slicing.
///
/// Takes the object length and 3 optional values and returns `(i64, i64, i64)`
/// with those index correctly converted in range of length.
/// Return the correct errors if the values are not numeric or the stride is 0.
///
/// # Examples
///
/// ```rust
/// # use starlark::values::*;
/// # use starlark::values::slice_indices::convert_slice_indices;
/// let six      = Some(Value::new(6));
/// let minusone = Some(Value::new(-1));
/// let ten      = Some(Value::new(10));
///
/// # assert!(
/// convert_slice_indices(7, six, None, None).unwrap() == (6, 7, 1)
/// # );
/// # assert!(
/// convert_slice_indices(7, minusone.clone(), None, minusone.clone()).unwrap()
///        == (6, -1, -1)
/// # );
/// # assert!(
/// convert_slice_indices(7, minusone, ten, None).unwrap() == (6, 7, 1)
/// # );
/// ```
pub fn convert_slice_indices(
    len: i64,
    start: Option<Value>,
    stop: Option<Value>,
    stride: Option<Value>,
) -> Result<(i64, i64, i64), ValueError> {
    let stride = stride.unwrap_or_else(|| Value::new(1));
    let stride = if stride.get_type() == "NoneType" {
        Ok(1)
    } else {
        stride.to_int()
    };
    match stride {
        Ok(0) => Err(ValueError::IndexOutOfBound(0)),
        Ok(stride) => {
            let def_start = if stride < 0 { len - 1 } else { 0 };
            let def_end = if stride < 0 { -1 } else { len };
            let clamp = if stride < 0 { -1 } else { 0 };
            let start = convert_index_aux(len, start, def_start, clamp, len + clamp);
            let stop = convert_index_aux(len, stop, def_end, clamp, len + clamp);
            match (start, stop) {
                (Ok(s1), Ok(s2)) => Ok((s1, s2, stride)),
                (Err(x), ..) => Err(x),
                (Ok(..), Err(x)) => Err(x),
            }
        }
        _ => Err(ValueError::IncorrectParameterType),
    }
}

#[cfg(test)]
mod test {
    use crate::values::error::ValueError;
    use crate::values::slice_indices::convert_slice_indices;
    use crate::values::Value;

    #[test]
    fn test_convert_slice_indices() {
        assert_eq!(Ok(6), Value::new(6).convert_index(7));
        assert_eq!(Ok(6), Value::new(-1).convert_index(7));
        assert_eq!(
            Ok((6, 7, 1)),
            convert_slice_indices(7, Some(Value::new(6)), None, None)
        );
        assert_eq!(
            Ok((6, -1, -1)),
            convert_slice_indices(7, Some(Value::new(-1)), None, Some(Value::new(-1)))
        );
        assert_eq!(
            Ok((6, 7, 1)),
            convert_slice_indices(7, Some(Value::new(-1)), Some(Value::new(10)), None)
        );
        // Errors
        assert_eq!(
            Err(ValueError::IncorrectParameterType),
            Value::from("a").convert_index(7)
        );
        assert_eq!(
            Err(ValueError::IndexOutOfBound(8)),
            Value::new(8).convert_index(7)
        );
        assert_eq!(
            Err(ValueError::IndexOutOfBound(-1)),
            Value::new(-8).convert_index(7)
        );
    }
}
