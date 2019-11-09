use crate::environment::Environment;
use crate::gc;
use crate::values::list::List;
use crate::values::ImmutableNoValues;
use crate::values::TypedValue;
use crate::values::Value;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Arc;

/// A value which increments a counter on drop
#[derive(Default)]
struct DropCanary {
    drop_count: Arc<AtomicUsize>,
}

impl TypedValue for DropCanary {
    type Holder = ImmutableNoValues<Self>;
    const TYPE: &'static str = "canary";
}

impl Drop for DropCanary {
    fn drop(&mut self) {
        if gc::verbose() {
            eprintln!("canary drop");
        }
        self.drop_count.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn immutable_no_values() {
    let env = Environment::new("test");
    let _g = gc::push_env(&env);

    assert_eq!(0, env.heap().0.borrow().known_objects.len());

    // immutable values without references are not recorded in heap
    Value::new(1);

    assert_eq!(0, env.heap().0.borrow().known_objects.len());
}

#[test]
fn immutable_with_values() {
    let env = Environment::new("test");
    let _g = gc::push_env(&env);

    assert_eq!(0, env.heap().0.borrow().known_objects.len());

    // immutable values with possible references are recorded in heap
    Value::from((10, "true"));

    assert_eq!(1, env.heap().0.borrow().known_objects.len());
    // object is recorded, but it is already destroyed
    assert!(env.heap().0.borrow().known_objects[0].upgrade().is_none());

    // explicitly call GC
    env.heap().gc(&env, "explicit");

    // and the object is gone
    assert_eq!(0, env.heap().0.borrow().known_objects.len());
}

#[test]
fn register_clears_old_weaks() {
    let env = Environment::new("test");
    let _g = gc::push_env(&env);

    for _ in 0..1000 {
        // create a new list, which immediately becomes a weak reference
        Value::from(Vec::<Value>::new());
        assert!(env.heap().0.borrow().known_objects.len() < 50);
    }
}

#[test]
fn cycle_is_cleared() {
    let env = Environment::new("test");
    let _g = gc::push_env(&env);

    assert_eq!(0, env.heap().0.borrow().known_objects.len());

    let list = Value::from(Vec::<Value>::new());
    // it is cyclic list now
    list.downcast_mut::<List>()
        .unwrap()
        .unwrap()
        .push(list.clone());

    assert_eq!(1, env.heap().0.borrow().known_objects.len());

    // keep a week reference to test later
    let list = {
        let list = list;
        list.to_gc_strong().unwrap().downgrade()
    };

    // heap still contains this object as alive because it references itself
    assert!(env.heap().0.borrow().known_objects[0]
        .clone()
        .upgrade()
        .is_some());

    env.heap().gc(&env, "explicit");

    // list is gone
    assert_eq!(0, env.heap().0.borrow().known_objects.len());
    // it is actually gone
    assert!(list.upgrade().is_none());
}

#[test]
fn list_in_tuple_is_dropped_after_freeze() {
    // ```
    // l = []
    // l.append(l)
    // global.t = (l,)
    // ```
    // Global variable is immutable, but holds a mutable object with cycles.
    // Test that object is dropped.

    let env = Environment::new("test");
    let g = gc::push_env(&env);

    let drop_canary = DropCanary::default();
    let drop_count = drop_canary.drop_count.clone();

    let l = List::new();
    l.downcast_mut::<List>().unwrap().unwrap().push(l.clone());
    l.downcast_mut::<List>()
        .unwrap()
        .unwrap()
        .push(Value::new(drop_canary));

    let t = Value::from((l,));
    env.set("t", t).unwrap();

    env.freeze(true);

    assert_eq!(0, drop_count.load(Ordering::SeqCst));
    drop(env);
    drop(g);
    assert_eq!(1, drop_count.load(Ordering::SeqCst));
}

#[test]
fn list_in_tuple_is_dropped_without_freeze() {
    // This scenario:
    // ```
    // l = []
    // l.append(l)
    // global.t = (l,)
    // ```
    // Global variable is immutable, but holds a mutable object with cycles.
    // Test that object is dropped.

    let env = Environment::new("test");
    let g = gc::push_env(&env);

    let drop_canary = DropCanary::default();
    let drop_count = drop_canary.drop_count.clone();

    let l = List::new();
    l.downcast_mut::<List>().unwrap().unwrap().push(l.clone());
    l.downcast_mut::<List>()
        .unwrap()
        .unwrap()
        .push(Value::new(drop_canary));

    let t = Value::from((l,));
    env.set("t", t).unwrap();

    assert_eq!(0, drop_count.load(Ordering::SeqCst));
    drop(env);
    drop(g);
    assert_eq!(1, drop_count.load(Ordering::SeqCst));
}

#[test]
fn imported_value_is_not_collected() {
    let parent = Environment::new("parent");
    let g = gc::push_env(&parent);

    let l = List::new();
    l.downcast_mut::<List>()
        .unwrap()
        .unwrap()
        .push(Value::from(17));
    parent.set("l", l).unwrap();

    drop(g);

    // `.child` does `freeze` which does GC
    let child = parent.child("child");

    // Parent still contains original list
    assert_eq!("[17]", parent.get("l").unwrap().to_str());

    child.set("l", parent.get("l").unwrap()).unwrap();
    // Do GC in child
    child.freeze(true);

    // Parent and child still contain original list
    assert_eq!("[17]", parent.get("l").unwrap().to_str());
    assert_eq!("[17]", child.get("l").unwrap().to_str());

    drop(child);
    // Parent value is not collected
    assert_eq!("[17]", parent.get("l").unwrap().to_str());
}

#[test]
fn child_env_prevents_parent_drop() {
    let parent = Environment::new("parent");
    let g = gc::push_env(&parent);

    let l = List::new();
    l.downcast_mut::<List>()
        .unwrap()
        .unwrap()
        .push(Value::from(19));
    parent.set("l", l).unwrap();

    drop(g);

    let child = parent.child("child");
    child.set("l", parent.get("l").unwrap()).unwrap();

    // Even if we no longer have a reference to parent,
    // child content has a reference, so `l` is not collected
    drop(parent);
    assert_eq!("[19]", child.get("l").unwrap().to_str());
}

#[test]
fn freeze_without_gc() {
    // This scenario:
    // ```
    // l = []
    // l.append(l)
    // global.t = (l,)
    // ```
    let env = Environment::new("test");
    let g = gc::push_env(&env);

    let drop_canary = DropCanary::default();
    let drop_count = drop_canary.drop_count.clone();

    let l = List::new();
    l.downcast_mut::<List>().unwrap().unwrap().push(l.clone());
    l.downcast_mut::<List>()
        .unwrap()
        .unwrap()
        .push(Value::new(drop_canary));

    let t = Value::from((l,));
    env.set("t", t).unwrap();

    // Freeze without GC
    env.freeze(false);

    // `t` and `l`
    assert_eq!(2, env.heap().0.borrow_mut().known_objects.len());

    drop(g);
    drop(env);
    assert_eq!(1, drop_count.load(Ordering::SeqCst));
}
