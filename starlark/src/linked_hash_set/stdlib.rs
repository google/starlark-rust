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

//! Methods for the `set` type.

use crate::values::hashed_value::HashedValue;
use crate::values::*;

use crate::linked_hash_set::value::Set;
use linked_hash_set::LinkedHashSet;

// Errors -- UF = User Failure -- Failure that should be expected by the user (e.g. from a fail()).
pub const SET_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE: &str = "UF30";

macro_rules! ok {
    ($e:expr) => {
        return Ok(Value::from($e));
    };
}

starlark_module! {global =>
    /// set: construct a set.
    ///
    /// `set(x)` returns a new set containing the elements of the
    /// iterable sequence x.
    ///
    /// With no argument, `set()` returns a new empty set.
    set(#a = None) {
        let mut s = LinkedHashSet::new();
        if a.get_type() != "NoneType" {
            for x in a.iter()? {
                s.insert_if_absent(HashedValue::new(x)?);
            }
        }
        ok!(s)
    }

    /// set.add: append an element to a set.
    ///
    /// `S.add(x)` adds `x` to the set S, and returns `None`.
    ///
    /// `add` fails if the set is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set()
    /// # (
    /// x.add(1) == None
    /// # and
    /// x.add(2) == None
    /// # and
    /// x.add(3) == None
    /// # and
    /// x.add(1) == None
    /// # and
    /// x == set([1, 2, 3])
    /// # )"#).unwrap());
    /// ```
    set.add(this, #el) {
        Set::insert_if_absent(&this, el)?;
        Ok(Value::new_imm(NoneValue))
    }

    /// set.clear: clear a set
    ///
    /// `S.clear()` removes all the elements of the set S and returns `None`.
    ///
    /// It fails if the set is frozen or if there are active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3])
    /// # (
    /// x.clear() == None
    /// # and
    /// x == set()
    /// # )"#).unwrap());
    /// ```
    set.clear(this) {
        Set::mutate(&this, &|x| {
            x.clear();
            Ok(Value::new_imm(NoneValue))
        })
    }

    /// set.copy: return a set containing all of the elements of this set, in the same order.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3])
    /// y = x.copy()
    /// x.add(4)
    /// y.add(5)
    /// # (
    /// x == set([1, 2, 3, 4])
    /// # and
    /// y == set([1, 2, 3, 5])
    /// # )"#).unwrap());
    /// ```
    set.copy(this) {
        let ret = Set::new_value(Default::default());
        for el in this.iter()? {
            Set::insert_if_absent(&ret, el)?;
        }
        ok!(ret)
    }

    /// set.difference: return a set containing all of the elements of this set, without any
    /// elements present in any of the passed sets.
    ///
    /// `S.difference(x, y)` returns `S - x - y`.
    ///
    /// `difference` fails if its argument(s) are not iterable.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// y = [1]
    /// z = set([2, 3])
    /// (
    /// x.difference(y, z) == set([4])
    /// # and
    /// x.difference() == x
    /// # and
    /// x == set([1, 2, 3, 4])
    /// # and
    /// y == [1]
    /// # and
    /// z == set([2, 3])
    /// # )"#).unwrap());
    /// ```
    set.difference(this, *others) {
        let ret = Set::new_value(Default::default());
        for el in this.iter()? {
            let mut is_in_any_other = false;
            for other in &others {
                if other.is_in(&el)? {
                    is_in_any_other = true;
                    break;
                }
            }
            if !is_in_any_other {
                Set::insert_if_absent(&ret, el)?;
            }
        }
        ok!(ret)
    }

    /// set.difference_update: remove all elements of another iterable from this set.
    ///
    /// `S.difference_update(x)` removes all values in x from S.
    ///
    /// `difference_update` fails if its argument is not iterable.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// x.difference_update(set([1]))
    /// x.difference_update([2, 3])
    /// x == set([4])
    /// # "#).unwrap());
    /// ```
    set.difference_update(this, #other) {
        let previous_length = this.length()? as usize;
        Set::mutate(&this, &|x| {
            let mut values = Vec::with_capacity(previous_length);
            for el in x.iter() {
                if !other.is_in(el.get_value())? {
                    values.push(el.clone());
                }
            }
            x.clear();
            for value in values.into_iter() {
                x.insert(value);
            }
            Ok(Value::new_imm(NoneValue))
        })
    }

    /// set.discard: remove a value from a set if it is present.
    ///
    /// `S.discard(x)` removes the the value `x` from the set S if it is present, and returns `None`.
    ///
    /// `discard` fails if the set is frozen, or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3])
    /// # (
    /// x.discard(2) == None
    /// # and
    /// x.discard(4) == None
    /// # and
    /// x == set([1, 3])
    /// # )"#).unwrap());
    /// ```
    set.discard(this, #needle) {
        Set::mutate(&this, &|x| {
            x.remove(&HashedValue::new(needle.clone())?);
            Ok(Value::new_imm(NoneValue))
        })
    }

    /// set.intersection: return a set containing all of the elements of this set which are also
    /// present in all of the passed iterables.
    ///
    /// `intersection` fails if its argument(s) are not iterable.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// y = [1, 2]
    /// z = set([2, 3])
    /// (
    /// x.intersection(y, z) == set([2])
    /// # and
    /// x.intersection() == x
    /// # and
    /// x.intersection().clear() == None
    /// # and
    /// x == set([1, 2, 3, 4])
    /// # and
    /// y == [1, 2]
    /// # and
    /// z == set([2, 3])
    /// # )"#).unwrap());
    /// ```
    set.intersection(this, *others) {
        let ret = Set::new_value(Default::default());
        for el in this.iter()? {
            let mut is_in_every_other = true;
            for other in &others {
                if !other.is_in(&el)? {
                    is_in_every_other = false;
                    break;
                }
            }
            if is_in_every_other {
                Set::insert_if_absent(&ret, el)?;
            }
        }
        ok!(ret)
    }

    /// set.intersection_update: remove all elements from this set which are not in the other
    /// iterable.
    ///
    /// `S.intersection_update(x)` removes all values not in x from S.
    ///
    /// `intersection_update` fails if its argument is not iterable.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// x.intersection_update(set([1, 2]))
    /// x.intersection_update([2, 3])
    /// x == set([2])
    /// # "#).unwrap());
    /// ```
    set.intersection_update(this, #other) {
        let previous_length = this.length()? as usize;
        Set::mutate(&this, &|x| {
            let mut values = Vec::with_capacity(previous_length);
            for el in x.iter() {
                if other.is_in(el.get_value())? {
                    values.push(el.clone());
                }
            }
            x.clear();
            for value in values.into_iter() {
                x.insert(value);
            }
            Ok(Value::new_imm(NoneValue))
        })
    }

    /// set.isdisjoint: return whether a set has no intersection with another set.
    ///
    /// `isdisjoint` fails if its argument is not a set.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// (
    /// x.isdisjoint(set()) == True
    /// # and
    /// x.isdisjoint(set([5])) == True
    /// # and
    /// x.isdisjoint(set([1])) == False
    /// # and
    /// x.isdisjoint(set([1, 5])) == False
    /// # )"#).unwrap());
    /// ```
    set.isdisjoint(this, #other) {
        ok!(Set::compare(&this, &other, &|s1, s2| Ok(s1.intersection(s2).next().is_none()))?)
    }

    /// set.issubset: return whether another set contains this set.
    ///
    /// `issubset` fails if its argument is not a set.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// (
    /// x.issubset(set()) == False
    /// # and
    /// x.issubset(set([1, 2, 3])) == False
    /// # and
    /// x.issubset(set([4, 3, 2, 1])) == True
    /// # and
    /// x.issubset(set([1, 2, 3, 4, 5])) == True
    /// # )"#).unwrap());
    /// ```
    set.issubset(this, #other) {
        ok!(Set::compare(&this, &other, &|this, other| Ok(this.is_subset(other)))?)
    }

    /// set.issubset: return whether this set contains another set.
    ///
    /// `issuperset` fails if its argument is not a set.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// (
    /// x.issuperset(set()) == True
    /// # and
    /// x.issuperset(set([1, 2, 3])) == True
    /// # and
    /// x.issuperset(set([4, 3, 2, 1])) == True
    /// # and
    /// x.issuperset(set([1, 2, 3, 4, 5])) == False
    /// # )"#).unwrap());
    /// ```
    set.issuperset(this, #other) {
        ok!(Set::compare(&this, &other, &|this, other| Ok(other.is_subset(this)))?)
    }

    /// set.pop: removes and returns the last element of a set.
    ///
    /// `S.pop([index])` removes and returns the last element of the set S, or,
    /// if the optional index is provided, at that index.
    ///
    /// `pop` fails if the index is negative or not less than the length of
    /// the set, of if the set is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// # (
    /// x.pop(1) == 2
    /// # and
    /// x.pop() == 4
    /// # and
    /// x.pop(0) == 1
    /// # and
    /// x == set([3])
    /// # )"#).unwrap());
    /// ```
    set.pop(this, #index = None) {
        let length = this.length()?;
        let index = if index.get_type() == "NoneType" {
            length - 1
        } else {
            index.to_int()?
        };
        if index < 0 || index >= length {
            return Err(ValueError::IndexOutOfBound(index));
        }
        let index = index as usize;
        Set::mutate(&this, &|x| {
            let ret = if index == (length - 1) as usize {
                x.pop_back()
            } else if index == 0 {
                x.pop_front()
            } else {
                let ret = x.iter().nth(index).cloned();
                let values: Vec<_> = x.iter().take(index).chain(x.iter().skip(index + 1)).cloned().collect();
                x.clear();
                for value in values.into_iter() {
                    x.insert(value);
                }
                ret
            };
            Ok(ret.unwrap().into())
        })
    }

    /// set.remove: remove a value from a set
    ///
    /// `S.remove(x)` removes the the value `x` from the set S, and returns `None`.
    ///
    /// `remove` fails if the set does not contain `x`, is frozen, or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3])
    /// # (
    /// x.remove(2) == None
    /// # and
    /// x == set([1, 3])
    /// # )"#).unwrap());
    /// ```
    ///
    /// A subsequent call to `x.remove(2)` would yield an error because the element won't be
    /// found.
    set.remove(this, #needle) {
        let did_remove = Set::mutate(&this, &|x| {
            ok!(x.remove(&HashedValue::new(needle.clone())?))
        });
        if did_remove?.to_bool() {
            Ok(Value::new_imm(NoneValue))
        } else {
            starlark_err!(
                SET_REMOVE_ELEMENT_NOT_FOUND_ERROR_CODE,
                format!("Element '{}' not found in '{}'", needle, this),
                "not found".to_owned()
            )
        }
    }

    /// set.symmetric_difference: return a set containing the elements present in exactly one of
    /// this and another set.
    ///
    /// `symmetric_difference` fails if its argument is not a set.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3, 4])
    /// y = set([0, 1, 2])
    /// z = set([5])
    /// (
    /// x.symmetric_difference(y) == set([3, 4, 0])
    /// # and
    /// y.symmetric_difference(x) == set([0, 3, 4])
    /// # and
    /// x.symmetric_difference(z) == set([1, 2, 3, 4, 5])
    /// # )"#).unwrap());
    /// ```
    set.symmetric_difference(this, #other) {
        Set::compare(&this, &other, &|s1, s2| {
            Ok(Set::from(s1.symmetric_difference(s2).cloned().collect()).unwrap())
        })
    }

    /// set.symmetric_difference_update: update this set to contain the symmetric difference of
    /// this and another set.
    ///
    /// `symmetric_difference_update` fails if its argument is not a set.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x1 = set([1, 2, 3, 4])
    /// x2 = set([1, 2, 3, 4])
    /// y = set([0, 1, 2])
    /// z = set([5])
    /// (
    /// x1.symmetric_difference_update(y) == None
    /// # and
    /// x1 == set([3, 4, 0])
    /// # and
    /// y == set([0, 1, 2])
    /// # and
    /// y.symmetric_difference_update(x2) == None
    /// # and
    /// y == set([0, 3, 4])
    /// # and
    /// x2 == set([1, 2, 3, 4])
    /// # and
    /// x2.symmetric_difference_update(z) == None
    /// # and
    /// x2 == set([1, 2, 3, 4, 5])
    /// # and
    /// z == set([5])
    /// # )"#).unwrap());
    /// ```
    set.symmetric_difference_update(this, #other) {
        let symmetric_difference = Set::compare(&this, &other, &|s1, s2| {
            Ok(Set::from(s1.symmetric_difference(s2).cloned().collect()).unwrap())
        })?;
        Set::mutate(&this, &|s| {
            s.clear();
            for item in symmetric_difference.iter()? {
                s.insert(HashedValue::new(item)?);
            }
            Ok(Value::new_imm(NoneValue))
        })
    }

    /// set.union: return a set containing all of the elements of this set, then all of the extra
    /// elements of the other iterables.
    ///
    /// `S.union(x, y)` returns a set of the union of `S` and `x` and `y`
    /// (which must be iterables)'s elements.
    ///
    /// `union` fails if its arguments are not iterable.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set([1, 2, 3])
    /// y = set([2, 4, 5])
    /// z = [5, 6]
    /// (
    /// x.union(y, z) == set([1, 2, 3, 4, 5, 6])
    /// # and
    /// x == set([1, 2, 3])
    /// # and
    /// y == set([2, 4, 5])
    /// # and
    /// z == [5, 6]
    /// # )"#).unwrap());
    /// ```
    set.union(this, *others) {
        let ret = Set::new_value(Default::default());
        for el in this.iter()? {
            Set::insert_if_absent(&ret, el)?;
        }
        for other in others {
            for el in other.iter()? {
                Set::insert_if_absent(&ret, el)?;
            }
        }
        ok!(ret)
    }

    /// set.update: update a set to also contain another iterable's content.
    ///
    /// `S.update(x)` adds the elements of `x`, which must be iterable, to
    /// the set S, and returns `None`.
    ///
    /// `update` fails if `x` is not iterable, or if the set S is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = set()
    /// # (
    /// x.update([1, 2, 3], set(["foo"])) == None
    /// # and
    /// x.update(["bar"]) == None
    /// # and
    /// x == set([1, 2, 3, "foo", "bar"])
    /// # )"#).unwrap());
    /// ```
    set.update(this, *others) {
        for other in others {
            for el in other.iter()? {
                Set::insert_if_absent(&this, el)?;
            }
        }
        Ok(Value::new_imm(NoneValue))
    }
}
