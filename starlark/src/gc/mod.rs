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

//! Garbage collector.

use crate::environment::Environment;
use crate::environment::TypeValues;
use crate::values::DataPtr;
use crate::values::ValueGcStrong;
use crate::values::ValueGcWeak;
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::HashSet;
use std::env;
use std::fmt;
use std::mem;
use std::rc::Rc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Once;
use std::time::Instant;

static INIT_VERBOSE_ONCE: Once = Once::new();
static VERBOSE: AtomicBool = AtomicBool::new(false);

/// Should GC be verbose?
fn verbose() -> bool {
    INIT_VERBOSE_ONCE.call_once(|| {
        VERBOSE.store(
            env::var("STARLARK_RUST_GC_VERBOSE").is_ok(),
            Ordering::Relaxed,
        )
    });
    VERBOSE.load(Ordering::Relaxed)
}

/// Make GC verbose (or not).
///
/// Override the value of `STARLARK_RUST_GC_VERBOSE` envrionment variable.
pub fn set_verbose(verbose: bool) {
    VERBOSE.store(verbose, Ordering::Relaxed);
}

thread_local! {
    /// Thread-local heap which is used to register newly created `Value` objects.
    static HEAP: Cell<Option<Heap>> = Cell::new(None);
}

struct HeapContent {
    /// name is for debugging
    name: String,
    /// Print statistics to stderr when on
    verbose: bool,
    /// All objects known to this heap, including unreachable
    known_objects: Vec<ValueGcWeak>,
    /// Number of object survived collection of weak references
    last_weak_gc_survivors: usize,
}

/// Known objects for the environment.
/// There's exactly one `Heap` exists for each `Environment`.
#[derive(Clone, Debug)]
pub struct Heap(Rc<RefCell<HeapContent>>);

impl Heap {
    pub(crate) fn new(name: &str) -> Heap {
        Heap(Rc::new(RefCell::new(HeapContent {
            name: name.to_owned(),
            verbose: verbose(),
            known_objects: Vec::new(),
            last_weak_gc_survivors: 0,
        })))
    }
}

impl HeapContent {
    fn gc(&mut self, roots: &Environment, reason: &str) {
        let start = if self.verbose {
            Some(Instant::now())
        } else {
            None
        };

        if self.verbose {
            eprintln!("GC {} start because {}", self.name, reason);
        }

        // Upgrade known objects to strong reference
        // * to obtain data pointers
        // * to collect them
        let known_objects: Vec<ValueGcStrong> = mem::replace(&mut self.known_objects, Vec::new())
            .into_iter()
            .flat_map(|v| v.upgrade())
            .collect();

        // Pointers to all objects known to this heap
        let known_object_ptrs: HashSet<DataPtr> =
            known_objects.iter().map(ValueGcStrong::data_ptr).collect();

        // GC roots
        let root_objects = roots.roots();

        // Mark phase

        // Objects reachable from roots
        let mut alive: HashSet<DataPtr> = HashSet::new();

        let mut queue = root_objects;
        while let Some(object) = queue.pop() {
            // Already seen the object
            if !alive.insert(object.data_ptr()) {
                continue;
            }

            object.visit_links(&mut |link| {
                let link = match link.to_gc_strong() {
                    Some(link) => link,
                    None => {
                        // GC doesn't care about ints or strings
                        return;
                    }
                };

                if !known_object_ptrs.contains(&link.data_ptr()) {
                    // Object from another heap
                    return;
                }

                queue.push(link);
            });
        }

        // Sweep phase

        let mut new_known_objects = Vec::new();
        for object in known_objects {
            if !alive.contains(&object.data_ptr()) {
                object.gc();
            } else {
                new_known_objects.push(object.downgrade());
            }
        }
        self.known_objects = new_known_objects;

        if let Some(start) = start {
            eprintln!("GC {} took {}us", self.name, start.elapsed().as_micros());
        }
    }

    fn gc_on_drop(&mut self) {
        if self.verbose {
            eprintln!(
                "GC {} on drop for {} objects...",
                self.name,
                self.known_objects.len()
            );
        }
        for object in mem::replace(&mut self.known_objects, Vec::new()) {
            let object = match object.upgrade() {
                Some(object) => object,
                None => continue,
            };
            object.gc();
        }
        if self.verbose {
            eprintln!("GC {} on drop done", self.name);
        }
    }

    /// Clean-up weak object references, not a proper GC.
    fn gc_weak(&mut self, reason: &str) {
        if self.verbose {
            eprintln!(
                "light GC {} because {} for {} weak references...",
                self.name,
                reason,
                self.known_objects.len()
            );
        }
        self.known_objects.retain(ValueGcWeak::is_alive);
        self.last_weak_gc_survivors = self.known_objects.len();
        if self.verbose {
            eprintln!(
                "light GC {} because {} survived {} objects",
                self.name,
                reason,
                self.known_objects.len()
            );
        }
    }

    fn gc_weak_if_needed(&mut self) {
        // Do GC only if number of object is twice as previously alive
        // to keep this operation constant
        if self.known_objects.len() >= 17
            && self.known_objects.len() >= self.last_weak_gc_survivors * 2
        {
            self.gc_weak("register");
        }
    }

    fn register(&mut self, object: ValueGcWeak) {
        self.gc_weak_if_needed();
        self.known_objects.push(object);
    }
}

impl fmt::Debug for HeapContent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("HeapContent")
            .field("name", &self.name)
            .field("verbose", &self.verbose)
            .field("objects", &self.known_objects.len())
            .field("last_weak_gc_survivors", &self.last_weak_gc_survivors)
            .finish()
    }
}

impl Drop for HeapContent {
    fn drop(&mut self) {
        self.gc_on_drop();
    }
}

impl Heap {
    pub fn gc(&self, roots: &Environment, reason: &str) {
        self.0.borrow_mut().gc(roots, reason)
    }

    pub fn gc_weak(&self, reason: &str) {
        self.0.borrow_mut().gc_weak(reason);
    }
}

pub(crate) fn register(object: ValueGcWeak) {
    with_heap(|heap| {
        heap.0.borrow_mut().register(object);
    });
}

struct SetOnDrop(Option<Heap>);

impl Drop for SetOnDrop {
    fn drop(&mut self) {
        HEAP.with(|cell| cell.set(mem::replace(&mut self.0, None)));
    }
}

/// Panics if thread-local heap is not set
fn with_heap<F, R>(f: F) -> R
where
    F: FnOnce(&Heap) -> R,
{
    HEAP.with(|cell| {
        let heap = cell.replace(None);
        let set_on_drop = SetOnDrop(heap);
        let heap = set_on_drop.0.as_ref().expect("thread-local GC is not set");
        f(heap)
    })
}

fn _heap() -> Option<Heap> {
    HEAP.with(|cell| {
        let heap = cell.replace(None);
        let set_on_drop = SetOnDrop(heap);
        set_on_drop.0.clone()
    })
}

/// Will reset previous environment on drop.
#[must_use]
pub struct HeapGuard(SetOnDrop);

/// Set a thread-local environment which is used for registration
/// of newly created values. Returned value restores previous heap value on drop.
pub fn push_env(env: &Environment) -> HeapGuard {
    let old_heap = HEAP.with(|cell| cell.replace(Some(env.heap())));
    HeapGuard(SetOnDrop(old_heap))
}

/// Set a thread-local environment which is used for registration
/// of newly created values. Returned value restores previous heap value on drop.
#[doc(hidden)] // used only from macros
pub fn push_type_values(type_values: &TypeValues) -> HeapGuard {
    let old_heap = HEAP.with(|cell| cell.replace(Some(type_values.heap())));
    HeapGuard(SetOnDrop(old_heap))
}

#[cfg(test)]
mod tests;
