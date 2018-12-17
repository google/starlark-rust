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

//! Methods for the `dict` type.

use linked_hash_map::LinkedHashMap;
use values::*;

pub const DICT_KEY_NOT_FOUND_ERROR_CODE: &'static str = "UF20";
pub const POP_ON_EMPTY_DICT_ERROR_CODE: &'static str = "UF21";

macro_rules! ok {
    ($e:expr) => {
        return Ok(Value::from($e));
    };
}

starlark_module!{global =>
    /// [dict.clear](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·clear
    /// ): clear a dictionary
    ///
    /// `D.clear()` removes all the entries of dictionary D and returns `None`.
    /// It fails if the dictionary is frozen or if there are active iterators.
    ///
    ///
    /// `dict·clear` is not provided by the Java implementation.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// x.clear()   # now x == {}
    /// # (x == {})"#).unwrap());
    /// ```
    dict.clear(this) {
        dict::Dictionary::mutate(
            &mut this,
            &|x: &mut LinkedHashMap<Value, Value>| -> ValueResult {
                x.clear();
                ok!(None)
            }
        )
    }

    /// [dict.get](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·get
    /// ): return an element from the dictionary.
    ///
    /// `D.get(key[, default])` returns the dictionary value corresponding to the given key.
    /// If the dictionary contains no such value, `get` returns `None`, or the
    /// value of the optional `default` parameter if present.
    ///
    /// `get` fails if `key` is unhashable.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.get("one") == 1
    /// # and
    /// x.get("three") == None
    /// # and
    /// x.get("three", 0) == 0
    /// # )"#).unwrap());
    /// ```
    dict.get(this, #key, #default = None) {
        match this.at(key) {
            Err(ValueError::KeyNotFound(..)) => Ok(default),
            x => x
        }
    }

    /// [dict.items](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·items
    /// ): get list of (key, value) pairs.
    ///
    /// `D.items()` returns a new list of key/value pairs, one per element in
    /// dictionary D, in the same order as they would be returned by a `for` loop.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.items() == [("one", 1), ("two", 2)]
    /// # )"#).unwrap());
    /// ```
    dict.items(this) {
        dict::Dictionary::apply(
            &this,
            &|x: &LinkedHashMap<Value, Value>| -> ValueResult {
                let v : Vec<Value> =
                    x.iter().map(|x| Value::from((x.0.clone(), x.1.clone()))).collect();
                ok!(v)
            }
        )
    }

    /// [dict.keys](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·keys
    /// ): get the list of keys of the dictionary.
    ///
    /// `D.keys()` returns a new list containing the keys of dictionary D, in the
    /// same order as they would be returned by a `for` loop.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.keys() == ["one", "two"]
    /// # )"#).unwrap());
    /// ```
    dict.keys(this) {
        let v : Vec<Value> = this.into_iter()?.collect();
        ok!(v)
    }

    /// [dict.pop](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·pop
    /// ): return an element and remove it from a dictionary.
    ///
    /// `D.pop(key[, default])` returns the value corresponding to the specified
    /// key, and removes it from the dictionary.  If the dictionary contains no
    /// such value, and the optional `default` parameter is present, `pop`
    /// returns that value; otherwise, it fails.
    ///
    /// `pop` fails if `key` is unhashable, or the dictionary is frozen or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.pop("one") == 1
    /// # and
    /// x == {"two": 2}
    /// # and
    /// x.pop("three", 0) == 0
    /// # )"#).unwrap());
    /// ```
    ///
    /// Failure:
    ///
    /// ```python
    /// x.pop("four")  # error: missing key
    /// ```
    dict.pop(this, #key, #default = None) {
        key.get_hash()?;  // ensure the key is hashable
        let key_error = format!("Key '{}' not found in '{}'", key.to_repr(), this.to_repr());
        dict::Dictionary::mutate(
            &mut this,
            &|x: &mut LinkedHashMap<Value, Value>| -> ValueResult {
                match x.remove(&key) {
                    Some(x) => Ok(x),
                    None => if default.get_type() == "NoneType" {
                        starlark_err!(
                            DICT_KEY_NOT_FOUND_ERROR_CODE,
                            key_error.clone(),
                            "not found".to_owned()
                        );
                    } else {
                        Ok(default.clone())
                    }
                }
            }
        )
    }

    /// [dict.popitem](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·popitem
    /// ): returns and removes the first key/value pair of a dictionary.
    ///
    /// `D.popitem()` returns the first key/value pair, removing it from the dictionary.
    ///
    /// `popitem` fails if the dictionary is empty, frozen, or has active iterators.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.popitem() == ("one", 1)
    /// # and
    /// x.popitem() == ("two", 2)
    /// # )"#).unwrap());
    /// ```
    ///
    /// Failure:
    ///
    /// ```python
    /// x.popitem()  # error: empty dict
    /// ```
    dict.popitem(this) {
        dict::Dictionary::mutate(
            &mut this,
            &|x: &mut LinkedHashMap<Value, Value>| -> ValueResult {
                match x.pop_front() {
                    Some(x) => ok!(x),
                    None => starlark_err!(
                        POP_ON_EMPTY_DICT_ERROR_CODE,
                        "Cannot .popitem() on an empty dictionary".to_owned(),
                        "empty dictionary".to_owned()
                    )
                }
            }
        )
    }

    /// [dict.setdefault](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·setdefault
    /// ): get a value from a dictionary, setting it to a new value if not present.
    ///
    /// `D.setdefault(key[, default])` returns the dictionary value corresponding to the given key.
    /// If the dictionary contains no such value, `setdefault`, like `get`,
    /// returns `None` or the value of the optional `default` parameter if
    /// present; `setdefault` additionally inserts the new key/value entry into the dictionary.
    ///
    /// `setdefault` fails if the key is unhashable or if the dictionary is frozen.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.setdefault("one") == 1
    /// # and
    /// x.setdefault("three", 0) == 0
    /// # and
    /// x == {"one": 1, "two": 2, "three": 0}
    /// # and
    /// x.setdefault("four") == None
    /// # and
    /// x == {"one": 1, "two": 2, "three": 0, "four": None}
    /// # )"#).unwrap());
    /// ```
    dict.setdefault(this, #key, #default = None) {
        key.get_hash()?; // Ensure the key is hashable
        let cloned_this = this.clone();
        dict::Dictionary::mutate(
            &mut this,
            &|x: &mut LinkedHashMap<Value, Value>| -> ValueResult {
                if let Some(r) = x.get(&key) {
                    return Ok(r.clone())
                }
                x.insert(key.clone(), default.clone_for_container(&cloned_this)?);
                Ok(default.clone())
            }
        )
    }

    /// [dict.update](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·update
    /// ): update values in the dictionary.
    ///
    /// `D.update([pairs][, name=value[, ...])` makes a sequence of key/value
    /// insertions into dictionary D, then returns `None.`
    ///
    /// If the positional argument `pairs` is present, it must be `None`,
    /// another `dict`, or some other iterable.
    /// If it is another `dict`, then its key/value pairs are inserted into D.
    /// If it is an iterable, it must provide a sequence of pairs (or other iterables of length 2),
    /// each of which is treated as a key/value pair to be inserted into D.
    ///
    /// For each `name=value` argument present, the name is converted to a
    /// string and used as the key for an insertion into D, with its corresponding
    /// value being `value`.
    ///
    /// `update` fails if the dictionary is frozen.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {}
    /// x.update([("a", 1), ("b", 2)], c=3)
    /// x.update({"d": 4})
    /// x.update(e=5)
    /// # (
    /// x == {"a": 1, "b": 2, "c": 3, "d": 4, "e": 5}
    /// # )"#).unwrap());
    /// ```
    dict.update(this, #pairs=None, **kwargs) {
        match pairs.get_type() {
            "NoneType" => (),
            "list" => for v in pairs.into_iter()? {
                if v.length()? != 2 {
                    starlark_err!(
                        INCORRECT_PARAMETER_TYPE_ERROR_CODE,
                        concat!(
                            "dict.update expect a list of pairsor a dictionary as first ",
                            "argument, got a list of non-pairs."
                        ).to_owned(),
                        "list of non-pairs".to_owned()
                    )
                }
                this.set_at(v.at(Value::new(0))?, v.at(Value::new(1))?)?;
            },
            "dict" => for k in pairs.into_iter()? {
                this.set_at(k.clone(), pairs.at(k)?)?
            },
            x => starlark_err!(
                INCORRECT_PARAMETER_TYPE_ERROR_CODE,
                format!(
                    concat!(
                        "dict.update expect a list or a dictionary as first argument, ",
                        "got a value of type {}."
                    ),
                    x
                ),
                format!("type {} while expected list or dict", x)
            )
        }

        for k in kwargs.into_iter()? {
            this.set_at(k.clone(), kwargs.at(k)?)?
        }
        ok!(None)
    }

    /// [dict.values](
    /// https://github.com/google/skylark/blob/3705afa472e466b8b061cce44b47c9ddc6db696d/doc/spec.md#dict·values
    /// ): get the list of values of the dictionary.
    ///
    /// `D.values()` returns a new list containing the dictionary's values, in the
    /// same order as they would be returned by a `for` loop over the
    /// dictionary.
    ///
    /// Examples:
    ///
    /// ```
    /// # use starlark::stdlib::starlark_default;
    /// # assert!(starlark_default(r#"
    /// x = {"one": 1, "two": 2}
    /// # (
    /// x.values() == [1, 2]
    /// # )"#).unwrap());
    /// ```
    dict.values(this) {
        dict::Dictionary::apply(
            &this,
            &|x: &LinkedHashMap<Value, Value>| -> ValueResult {
                let v : Vec<Value> = x.iter().map(|x| x.1.clone()).collect();
                ok!(v)
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::super::starlark_default;
    use super::super::tests::starlark_default_fail;
    use super::*;

    macro_rules! starlark_ok {
        ($($t:expr),+) => (starlark_ok_fn!(starlark_default, $($t),+))
    }

    macro_rules! starlark_fail {
        ($($t:expr),+) => (starlark_fail_fn!(starlark_default_fail, $($t),+))
    }

    #[test]
    fn test_clear() {
        starlark_ok!(r#"x = {"one": 1, "two": 2}; x.clear(); (x == {})"#);
    }

    #[test]
    fn test_get() {
        starlark_ok!(
            r#"x = {"one": 1, "two": 2}; (
            x.get("one") == 1 and x.get("three") == None and x.get("three", 0) == 0)"#
        );
    }

    #[test]
    fn test_items() {
        starlark_ok!(r#"x = {"one": 1, "two": 2}; (x.items() == [("one", 1), ("two", 2)])"#);
    }

    #[test]
    fn test_keys() {
        starlark_ok!(r#"x = {"one": 1, "two": 2}; (x.keys() == ["one", "two"])"#);
    }

    #[test]
    fn test_pop() {
        starlark_ok!(
            r#"x = {"one": 1, "two": 2}; (
            x.pop("one") == 1 and x == {"two": 2} and x.pop("three", 0) == 0)"#
        );
        starlark_fail!(
            r#"x = {"one": 1}; x.pop("four")"#,
            DICT_KEY_NOT_FOUND_ERROR_CODE
        );
    }

    #[test]
    fn test_popitem() {
        starlark_ok!(
            r#"x = {"one": 1, "two": 2}; (
            x.popitem() == ("one", 1) and x.popitem() == ("two", 2))"#
        );
        starlark_fail!(r#"x = {}; x.popitem()"#, POP_ON_EMPTY_DICT_ERROR_CODE);
    }

    #[test]
    fn test_setdefault() {
        starlark_ok!(
            r#"x = {"one": 1, "two": 2}; (
            x.setdefault("one") == 1 and
            x.setdefault("three", 0) == 0 and
            x == {"one": 1, "two": 2, "three": 0} and
            x.setdefault("four") == None and
            x == {"one": 1, "two": 2, "three": 0, "four": None })"#
        );
    }

    #[test]
    fn test_update() {
        starlark_ok!(
            r#"
x = {}
x.update([("a", 1), ("b", 2)], c=3)
x.update({"d": 4})
x.update(e=5)
(x == {"a": 1, "b": 2, "c": 3, "d": 4, "e": 5})"#
        );
    }

    #[test]
    fn test_values() {
        starlark_ok!(r#"x = {"one": 1, "two": 2}; (x.values() == [1, 2])"#);
    }
}
