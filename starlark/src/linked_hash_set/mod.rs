use crate::environment::{Environment, TypeValues};

pub(crate) mod set_impl;
mod stdlib;
pub(crate) mod value;

/// Include `set` constructor and set functions in environment.
pub fn global(env: &mut Environment, type_values: &mut TypeValues) {
    self::stdlib::global(env, type_values);
    env.enable_set_literals();
}
