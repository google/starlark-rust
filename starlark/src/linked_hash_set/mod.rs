use crate::environment::Environment;
use crate::environment::TypeValues;

pub(crate) mod set_impl;
mod stdlib;
pub(crate) mod value;

/// Include `set` constructor and set functions in environment.
pub fn global(env: &mut Environment, type_values: &mut TypeValues) {
    self::stdlib::global(env, type_values);

    env.with_set_constructor(Box::new(crate::linked_hash_set::value::Set::from));

    value::global(type_values);
}
