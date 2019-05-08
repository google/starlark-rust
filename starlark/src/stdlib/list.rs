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

//! Methods for the `list` type.

use crate::values::list::List;
use crate::values::none::NoneType;
use crate::values::*;

// Errors -- UF = User Failure -- Failure that should be expected by the user (e.g. from a fail()).
pub const LIST_INDEX_FAILED_ERROR_CODE: &str = "UF10";
pub const LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE: &str = "UF11";

starlark_module! {global =>
    /// [list.append](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·append
    /// ): append an element to a list.
    ///
    /// `L.append(x)` appends `x` to the list L, and returns `None`.
    ///
    /// `append` fails if the list is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = []
    /// # (
    /// x.append(1) == None
    /// # and
    /// x.append(2) == None
    /// # and
    /// x.append(3) == None
    /// # and
    /// x == [1, 2, 3]
    /// # )"#).unwrap());
    /// ```
    list.append(this, #el) {
        let mut this = this.downcast_mut::<List>()?.unwrap();
        this.push(el)?;
        Ok(Value::new(NoneType::None))
    }

    /// [list.clear](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·clear
    /// ): clear a list
    ///
    /// `L.clear()` removes all the elements of the list L and returns `None`.
    /// It fails if the list is frozen or if there are active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = [1, 2, 3]
    /// x.clear()
    /// # (
    /// x == []
    /// # )"#).unwrap());
    /// ```
    list.clear(this) {
        let mut this = this.downcast_mut::<List>()?.unwrap();
        this.clear();
        Ok(Value::new(NoneType::None))
    }

    /// [list.extend](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·extend
    /// ): extend a list with another iterable's content.
    ///
    /// `L.extend(x)` appends the elements of `x`, which must be iterable, to
    /// the list L, and returns `None`.
    ///
    /// `extend` fails if `x` is not iterable, or if the list L is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = []
    /// # (
    /// x.extend([1, 2, 3]) == None
    /// # and
    /// x.extend(["foo"]) == None
    /// # and
    /// x == [1, 2, 3, "foo"]
    /// # )"#).unwrap());
    /// ```
    list.extend(this, #other) {
        let mut this = this.downcast_mut::<List>()?.unwrap();
        this.extend(other)?;
        Ok(Value::new(NoneType::None))
    }

    /// [list.index](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·index
    /// ): get the index of an element in the list.
    ///
    /// `L.index(x[, start[, end]])` finds `x` within the list L and returns its index.
    ///
    /// The optional `start` and `end` parameters restrict the portion of
    /// list L that is inspected.  If provided and not `None`, they must be list
    /// indices of type `int`. If an index is negative, `len(L)` is effectively
    /// added to it, then if the index is outside the range `[0:len(L)]`, the
    /// nearest value within that range is used; see [Indexing](#indexing).
    ///
    /// `index` fails if `x` is not found in L, or if `start` or `end`
    /// is not a valid index (`int` or `None`).
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = ["b", "a", "n", "a", "n", "a"]
    /// # (
    /// x.index("a") == 1      # bAnana
    /// # and
    /// x.index("a", 2) == 3   # banAna
    /// # and
    /// x.index("a", -2) == 5  # bananA
    /// # )"#).unwrap());
    /// ```
    list.index(this, #needle, #start = 0, #end = NoneType::None) {
        convert_indices!(this, start, end);
        let it = this.iter()?;
        let mut it = it.iter().skip(start).take(end - start);
        if let Some(offset) = it.position(|x| x == needle) {
            Ok(Value::new((offset + start) as i64))
        } else {
            starlark_err!(
                LIST_INDEX_FAILED_ERROR_CODE,
                format!("Element '{}' not found in '{}'", needle, this),
                "not found".to_owned()
            );
        }
    }

    /// [list.insert](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·insert
    /// ): insert an element in a list.
    ///
    /// `L.insert(i, x)` inserts the value `x` in the list L at index `i`, moving
    /// higher-numbered elements along by one.  It returns `None`.
    ///
    /// As usual, the index `i` must be an `int`. If its value is negative,
    /// the length of the list is added, then its value is clamped to the
    /// nearest value in the range `[0:len(L)]` to yield the effective index.
    ///
    /// `insert` fails if the list is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = ["b", "c", "e"]
    /// x.insert(0, "a")
    /// x.insert(-1, "d")
    /// # (
    /// x == ["a", "b", "c", "d", "e"]
    /// # )"#).unwrap());
    /// ```
    list.insert(this, #index, #el) {
        let mut this = this.downcast_mut::<List>()?.unwrap();
        convert_indices!(this, index);
        this.insert(index, el)?;
        Ok(Value::new(NoneType::None))
    }

    /// [list.pop](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·pop
    /// ): removes and returns the last element of a list.
    ///
    /// `L.pop([index])` removes and returns the last element of the list L, or,
    /// if the optional index is provided, at that index.
    ///
    /// `pop` fails if the index is negative or not less than the length of
    /// the list, of if the list is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = [1, 2, 3]
    /// # (
    /// x.pop() == 3
    /// # and
    /// x.pop() == 2
    /// # and
    /// x == [1]
    /// # )"#).unwrap());
    /// ```
    list.pop(this, ?#index) {
        let mut this = this.downcast_mut::<List>()?.unwrap();
        let index = match index {
            Some(index) => index.to_int()?,
            None => this.length()? - 1,
        };
        Ok(this.pop(index)?)
    }

    /// [list.remove](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#list·remove
    /// ): remove a value from a list
    ///
    /// `L.remove(x)` removes the first occurrence of the value `x` from the list L, and returns `None`.
    ///
    /// `remove` fails if the list does not contain `x`, is frozen, or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = [1, 2, 3, 2]
    /// x.remove(2)
    /// # t = (
    /// x == [1, 3, 2]
    /// # )
    /// x.remove(2)
    /// # (t and (
    /// x == [1, 3]
    /// # ))"#).unwrap());
    /// ```
    ///
    /// A subsequence call to `x.remove(2)` would yield an error because the element won't be
    /// found.
    /// ```
    list.remove(this, #needle) {
        let mut this = this.downcast_mut::<List>()?.unwrap();
        this.remove(needle)?;
        Ok(Value::new(NoneType::None))
    }
}

#[cfg(test)]
mod tests {
    use super::super::starlark_default;
    use super::super::tests::starlark_default_fail;
    use super::LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE;

    macro_rules! starlark_ok {
        ($($t:expr),+) => (starlark_ok_fn!(starlark_default, $($t),+))
    }

    macro_rules! starlark_fail {
        ($($t:expr),+) => (starlark_fail_fn!(starlark_default_fail, $($t),+))
    }

    #[test]
    fn test_append() {
        starlark_ok!(r#"x = []; x.append(1); x.append(2); x.append(3); (x == [1, 2, 3])"#);
    }

    #[test]
    fn test_clear() {
        starlark_ok!(r#"x = [1, 2, 3]; x.clear(); (x == [])"#);
    }

    #[test]
    fn test_extend() {
        starlark_ok!(r#"x = []; x.extend([1, 2, 3]); x.extend(["foo"]); (x == [1, 2, 3, "foo"])"#);
    }

    #[test]
    fn test_index() {
        starlark_ok!(
            r#"x = ["b", "a", "n", "a", "n", "a"]; (
            x.index("a") == 1 and x.index("a", 2) == 3 and x.index("a", -2) == 5)"#
        );
    }

    #[test]
    fn test_insert() {
        starlark_ok!(
            r#"x = ["b", "c", "e"]; x.insert(0, "a"); x.insert(-1, "d"); (
            x == ["a", "b", "c", "d", "e"])"#
        );
    }

    #[test]
    fn test_pop() {
        starlark_ok!(r#"x = [1, 2, 3]; x.pop() == 3"#);
        starlark_ok!(r#"x = [1, 2, 3]; (x.pop() == 3 and x.pop() == 2 and x == [1])"#);
    }

    #[test]
    fn test_remove() {
        starlark_ok!(
            r#"x = [1, 2, 3, 2]
x.remove(2); t1 = x == [1, 3, 2]
x.remove(2); t2 = x == [1, 3]
(t1 and t2)"#
        );
        starlark_fail!(
            r#"x = [1, 2, 3, 2]; x.remove(2); x.remove(2); x.remove(2)"#,
            LIST_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE
        );
    }
}
