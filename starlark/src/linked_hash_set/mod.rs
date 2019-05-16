use crate::environment::Environment;

pub(crate) mod set_impl;
mod stdlib;
pub(crate) mod value;

/// Include `set` constructor and set functions in environment.
pub fn global(env: Environment) -> Environment {
    let env = stdlib::global(env);
    env.with_set_constructor(Box::new(crate::linked_hash_set::value::Set::from));
    env
}
