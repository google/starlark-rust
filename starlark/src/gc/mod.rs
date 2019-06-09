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

use crate::environment::{Environment, EnvironmentWeak};
use crate::eval::{VarMap, VarMapWeak};
use crate::starlark_fun;
use crate::starlark_module;
use crate::starlark_param_name;
use crate::starlark_parse_param_type;
use crate::starlark_signature;
use crate::starlark_signature_extraction;
use crate::starlark_signatures;
use crate::values::none::NoneType;
use crate::values::{Value, ValueWeak};
use std::cell::{Cell, RefCell};
use std::rc::{Rc, Weak};
use std::time::Instant;
use std::{cmp, env, fmt, mem};

thread_local! { static HEAP: Cell<Option<Heap>> = Cell::new(None); }

/// On even iterations we mark objects with `Even` mark
/// and on `Odd` iterations with `Odd` mark.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Mark {
    Odd,
    Even,
}

impl Default for Mark {
    fn default() -> Self {
        Mark::Odd
    }
}

impl Mark {
    fn flip(self) -> Mark {
        match self {
            Mark::Even => Mark::Odd,
            Mark::Odd => Mark::Even,
        }
    }
}

/// Object GC state.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum GcState {
    /// Object is not registered in GC. Object is not "alive" yet.
    Unregistered,
    /// Object is marked (just registered in GC or survived last GC).
    Marked(Mark),
    /// Object is garbage collected.
    Collected,
}

impl Default for GcState {
    fn default() -> Self {
        GcState::Unregistered
    }
}

/// GC header of a value.
#[derive(Default)]
pub struct GcHeader {
    mark: Cell<GcState>,
}

/// Holder of GC header.
pub trait GcHeaderCell {
    /// Create a new cell.
    fn new() -> Self;

    /// Get GC header, of `None` if object is not garbage-collectable.
    fn get_gc_header(&self) -> Option<&GcHeader>;

    /// Assert the object is alive. This is used mainly for debugging.
    ///
    /// # Panics
    ///
    /// If object is not yet registered in GC or if it already collected.
    fn assert_alive(&self, t: &str);
}

/// Mutable object GC header.
#[derive(Default)]
pub struct GcHeaderMutable {
    gc_header: GcHeader,
}

impl GcHeaderCell for GcHeaderMutable {
    fn new() -> Self {
        Default::default()
    }

    fn get_gc_header(&self) -> Option<&GcHeader> {
        Some(&self.gc_header)
    }

    fn assert_alive(&self, t: &str) {
        match self.gc_header.mark.get() {
            GcState::Marked(_) => {}
            s => panic!("not alive: {}: {:?}", t, s),
        };
    }
}

/// GC header for objects without outgoing links.
/// Such objects need not be be garbage collected, refcounters works fine with them.
#[derive(Default)]
pub struct GcHeaderNoValue;

impl GcHeaderCell for GcHeaderNoValue {
    fn get_gc_header(&self) -> Option<&GcHeader> {
        None
    }

    fn new() -> Self {
        Default::default()
    }

    fn assert_alive(&self, _: &str) {}
}

#[derive(Default)]
struct HeapContent {
    /// GC is paused
    paused: bool,
    /// Print some debugging information during GC
    verbose: bool,
    /// Root environments
    root_envs: Vec<EnvironmentWeak>,
    /// Root local variables
    root_locals: Vec<VarMapWeak>,
    /// Root temporary values
    root_temporaries: Vec<TemporariesWeak>,
    /// All objects known to GC
    objects: Vec<ValueWeak>,
    /// Survivors of last GC
    last_gc_survivors: usize,
    /// Number of links from objects surviving last GC
    last_gc_reachable_links: usize,
    /// Last GC mark
    last_gc_mark: Mark,
    /// Number of objects registered since creation of the heap
    registered: u64,
    /// Number of objects registered since last GC run
    registered_since_last_gc: u64,
    /// Number of times GC ran
    gc_count: u64,
}

/// Garbage-collected objects
#[derive(Clone, Debug)]
pub struct Heap(Rc<RefCell<HeapContent>>);

impl Default for Heap {
    fn default() -> Self {
        let mut heap_content = HeapContent::default();
        if env::var("STARLARK_RUST_GC_VERBOSE").is_ok() {
            heap_content.verbose = true;
        }
        Heap(Rc::new(RefCell::new(heap_content)))
    }
}

pub(crate) trait GcRoots: Sized {
    /// Weak object for thess roots
    type Weak;

    /// Upgrade weak to strong
    fn upgrade(weak: Self::Weak) -> Option<Self>;

    /// Downgrade strong to weak
    fn downgrade(strong: &Self) -> Self::Weak;

    /// Collect objects from the roots
    fn roots(strong: &Self, roots: &mut Vec<Value>);
}

impl HeapContent {
    fn gc_get_roots_from_field<H: GcRoots>(
        root_holders: &mut Vec<H::Weak>,
        root_objects: &mut Vec<Value>,
    ) -> usize {
        let mut roots_dropped = 0;
        let mut new_root_holders = Vec::new();
        for root in mem::replace(root_holders, Vec::new()) {
            let root = match H::upgrade(root) {
                Some(root) => root,
                None => {
                    // It's OK if the "roots" is already dropped.
                    roots_dropped += 1;
                    continue;
                }
            };

            H::roots(&root, root_objects);

            new_root_holders.push(H::downgrade(&root));
        }
        *root_holders = new_root_holders;
        roots_dropped
    }

    /// Collect all objects from all roots.
    fn gc_get_roots(&mut self) -> Vec<Value> {
        let mut root_objects = Vec::new();

        let root_envs_dropped =
            Self::gc_get_roots_from_field::<Environment>(&mut self.root_envs, &mut root_objects);
        let root_locals_dropped =
            Self::gc_get_roots_from_field::<VarMap>(&mut self.root_locals, &mut root_objects);
        let root_temporaries_dropped = Self::gc_get_roots_from_field::<Temporaries>(
            &mut self.root_temporaries,
            &mut root_objects,
        );

        if self.verbose {
            eprintln!("{} root envs dropped", root_envs_dropped);
            eprintln!("{} root envs survived", self.root_envs.len());
            eprintln!("{} root local maps dropped", root_locals_dropped);
            eprintln!("{} root local maps survived", self.root_locals.len());
            eprintln!("{} root temporaries dropped", root_temporaries_dropped);
            eprintln!("{} root temporaries survived", self.root_temporaries.len());
            eprintln!("{} root objects found", root_objects.len());
        }
        root_objects
    }

    fn mark(&mut self, root_objects: Vec<Value>, new_mark: Mark) -> usize {
        let mut queue = root_objects;
        let mut reachable: usize = 0;
        let mut reachable_links: usize = 0;
        while let Some(object) = queue.pop() {
            let gc_header = match object.get_gc_header() {
                Some(gc_header) => gc_header,
                None => {
                    // Ignore plain refcounted objects
                    continue;
                }
            };
            match gc_header.mark.get() {
                GcState::Marked(_) => {}
                s => {
                    // All reachable objects must be alive,
                    // otherwise it is a bug somewhere.
                    panic!("wrong state: {:?}", s)
                }
            };
            gc_header.mark.set(GcState::Marked(new_mark));

            object.visit_links(&mut |link| {
                let link_gc_header = match link.get_gc_header() {
                    Some(gc_header) => gc_header,
                    None => return,
                };
                match link_gc_header.mark.get() {
                    GcState::Marked(mark) => {
                        if mark != new_mark {
                            reachable += 1;
                            link_gc_header.mark.set(GcState::Marked(new_mark));
                            queue.push(link.clone());
                        }
                        reachable_links += 1;
                    }
                    _ => {
                        // All reachable objects must be alive,
                        // otherwise it is a bug somewhere.
                        panic!()
                    }
                };
            });
        }

        if self.verbose {
            eprintln!("{} reachable objects found", reachable);
            eprintln!("{} reachable links", reachable_links);
        }

        reachable_links
    }

    fn sweep(&mut self, new_mark: Mark) -> (usize, usize) {
        let mut weak_cleared: usize = 0;
        let mut collected: usize = 0;

        let mut new_objects = Vec::new();
        for object in mem::replace(&mut self.objects, Vec::new()) {
            let object = match object.upgrade() {
                Some(object) => object,
                None => {
                    // Object is already dead by refcounting.
                    weak_cleared += 1;
                    continue;
                }
            };
            let gc_header = object.get_gc_header().expect("immutable object registered");
            match gc_header.mark.get() {
                GcState::Marked(mark) => {
                    if mark != new_mark {
                        // Collecting the object

                        if self.verbose {
                            eprintln!("collecting {}", object.debug_str());
                        }

                        collected += 1;
                        gc_header.mark.set(GcState::Collected);
                        object.gc();
                    } else {
                        // The object is still alive

                        new_objects.push(object.downgrade());
                    }
                }
                s => panic!("wrong state: {:?}", s),
            };
        }

        self.objects = new_objects;

        (weak_cleared, collected)
    }

    fn gc(&mut self, reason: &str) {
        let start = Instant::now();

        if self.verbose {
            eprintln!("GC start because {}", reason);
        }

        // Collect all GC roots
        let root_objects = self.gc_get_roots();

        // New "mark"
        let new_mark = self.last_gc_mark.flip();

        // Mark phase
        let reachable_links = self.mark(root_objects, new_mark);

        // Sweep phase
        let (weak_cleared, collected) = self.sweep(new_mark);

        self.last_gc_mark = new_mark;
        self.last_gc_survivors = self.objects.len();
        self.last_gc_reachable_links = reachable_links;
        self.gc_count += 1;
        self.registered_since_last_gc = 0;

        if self.verbose {
            eprintln!("weak cleared: {:?}", weak_cleared);
            eprintln!("collected:    {:?}", collected);
            eprintln!("mark:         {:?}", self.last_gc_mark);
            eprintln!("survivors:    {}", self.objects.len());
            eprintln!("iteration:    {:?}", start.elapsed());
            eprintln!("GC is done");
        }
    }

    fn gc_if_needed(&mut self) {
        // We need to preserve two basic constraints:
        // * Amortized GC time should be linear of number of allocated objects
        // * Memory overhead should be linear of memory used by live objects
        //
        // GC time is
        // `O(number of objects + number of outgoing links in objects)`.
        // And memory used by alive object is also
        // `O(number of objects + number of outgoing links in objects)`.
        //
        // So this very simple heuristic makes GC not necessarily very cheap,
        // but asymptotically correct with constraints specified above.

        if self.objects.len()
            >= cmp::max(
                (self.last_gc_survivors + self.last_gc_reachable_links) * 2,
                1,
            )
        {
            if self.verbose {
                eprintln!(
                    "triggering GC because objects {} is more than twice last survivors {}",
                    self.objects.len(),
                    self.last_gc_survivors
                );
            }
            self.gc("gc_if_needed");
        }
    }

    fn gc_on_drop(&mut self) {
        if self.verbose {
            eprintln!("GC on drop");
        }

        for value in mem::replace(&mut self.objects, Vec::new()) {
            if let Some(value) = value.upgrade() {
                value.gc();
            }
        }
    }

    fn register(&mut self, object: &Value, gc_header: &GcHeader) {
        self.objects.push(object.downgrade());
        self.registered += 1;
        self.registered_since_last_gc += 1;
        assert_eq!(GcState::Unregistered, gc_header.mark.get());
        gc_header.mark.set(GcState::Marked(self.last_gc_mark));
    }

    fn print_stats(&self) {
        println!("GC stats:");
        println!("paused:                   {}", self.paused);
        println!("weak objects:             {}", self.objects.len());
        println!("last GC survivors:        {}", self.last_gc_survivors);
        println!("GC count:                 {:?}", self.gc_count);
        println!("last mark:                {:?}", self.last_gc_mark);
        println!("registered:               {:?}", self.registered);
        println!(
            "registered since last GC: {:?}",
            self.registered_since_last_gc
        );
    }
}

impl fmt::Debug for HeapContent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("HeapContent")
            .field("paused", &self.paused)
            .field("root_envs", &self.root_envs.len())
            .field("objects", &self.objects.len())
            .field("last_gc_survivors", &self.last_gc_survivors)
            .field("last_gc_mark", &self.last_gc_mark)
            .field("registered", &self.registered)
            .field("registered_since_last_gc", &self.registered_since_last_gc)
            .field("gc_count", &self.gc_count)
            .finish()
    }
}

impl Drop for HeapContent {
    fn drop(&mut self) {
        self.gc_on_drop();
    }
}

impl Heap {
    /// Explicitly invoke GC
    pub fn gc(&self, reason: &str) {
        self.0.borrow_mut().gc(reason)
    }

    /// Invoke GC if significant number of objects allocated since last GC
    pub fn gc_if_needed(&self) {
        self.0.borrow_mut().gc_if_needed()
    }

    /// Register an environment as GC root
    pub(crate) fn register_env(&self, root: &Environment) {
        self.0
            .borrow_mut()
            .root_envs
            .push(Environment::downgrade(root));
    }

    /// Register local variables as GC root
    pub(crate) fn register_local_map(&self, locals: &VarMap) {
        self.0
            .borrow_mut()
            .root_locals
            .push(VarMap::downgrade(locals));
    }

    /// Register temporaries as GC root
    pub(crate) fn register_temporaries(&self, root: &Temporaries) {
        self.0
            .borrow_mut()
            .root_temporaries
            .push(Temporaries::downgrade(root));
    }
}

/// Register an object in thread-local heap.
///
/// # Panics
///
/// If thread-local heap is not set.
pub fn register(object: &Value) {
    let gc_header = match object.get_gc_header() {
        Some(gc_header) => gc_header,
        None => {
            // no-op if object does not need to be garbage collected
            // (e. g. refcounter is enough for `str`).
            return;
        }
    };

    with_heap(|heap| {
        heap.0.borrow_mut().register(object, gc_header);
    });
}

struct SetOnDrop(Option<Heap>);

impl Drop for SetOnDrop {
    fn drop(&mut self) {
        HEAP.with(|cell| cell.set(mem::replace(&mut self.0, None)));
    }
}

/// Panics is thread-local heap is not set
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

fn heap() -> Option<Heap> {
    HEAP.with(|cell| {
        let heap = cell.replace(None);
        let set_on_drop = SetOnDrop(heap);
        set_on_drop.0.clone()
    })
}

pub fn gc_if_needed() {
    with_heap(|heap| heap.gc_if_needed());
}

/// Restore previous heap on drop.
#[must_use]
pub struct HeapGuard(SetOnDrop);

/// Set heap as current thread-local heap.
///
/// Newly created `Value` objects are registed in this thread-local heap.
pub fn push_heap(heap: Heap) -> HeapGuard {
    let old_heap = HEAP.with(|cell| cell.replace(Some(heap)));
    HeapGuard(SetOnDrop(old_heap))
}

#[derive(Default)]
struct TemporariesContent {
    temporaries: Vec<Value>,
}

/// Storage for temporary objects which should survive GC.
///
/// Consider this starlark code:
///
/// ```ignore
/// a = ([], foo())
/// ```
///
/// After list is created, it is not store in any local variable,
/// and after list is created, function `foo()` is invoked,
/// which might trigger GC. So list need to be kept alive.
///
/// So tuple AST evaluation puts list into `Temporaries` objects.
#[derive(Default, Clone)]
pub(crate) struct Temporaries(Rc<RefCell<TemporariesContent>>);

#[derive(Default, Clone)]
pub(crate) struct TemporariesWeak(Weak<RefCell<TemporariesContent>>);

impl Temporaries {
    pub(crate) fn add(&self, value: Value) {
        self.0.borrow_mut().temporaries.push(value);
    }

    pub(crate) fn add_all<I: IntoIterator<Item = Value>>(&self, values: I) {
        for value in values {
            self.add(value);
        }
    }
}

impl GcRoots for Temporaries {
    type Weak = TemporariesWeak;

    fn upgrade(weak: TemporariesWeak) -> Option<Temporaries> {
        weak.0.upgrade().map(Temporaries)
    }

    fn downgrade(strong: &Temporaries) -> TemporariesWeak {
        TemporariesWeak(Rc::downgrade(&strong.0))
    }

    fn roots(strong: &Temporaries, roots: &mut Vec<Value>) {
        roots.extend(strong.0.borrow_mut().temporaries.iter().cloned())
    }
}

starlark_module! { globals =>
    print_gc_stats() {
        heap().unwrap().0.borrow().print_stats();
        Ok(Value::new(NoneType::None))
    }

    /// Explicitly invoke GC.
    gc_() {
        heap().unwrap().0.borrow_mut().gc("api");
        Ok(Value::new(NoneType::None))
    }

    /// Configure gc.
    gc_conf(?verbose: Option<bool>, ?paused: Option<bool>) {
        let heap = heap();
        let heap = heap.unwrap();
        let mut heap = heap.0.borrow_mut();
        if let Some(verbose) = verbose {
            heap.verbose = verbose;
        }
        if let Some(paused) = paused {
            heap.paused = paused;
        }
        Ok(Value::new(NoneType::None))
    }
}

#[cfg(test)]
mod tests {
    use crate::gc::{push_heap, Heap};
    use crate::values::list::List;
    use crate::values::Value;

    #[test]
    fn immutable_no_values() {
        let heap = Heap::default();
        let _heap_guard = push_heap(heap.clone());

        assert_eq!(0, heap.0.borrow().objects.len());

        // immutable values without references are not recorded in heap
        Value::new(1);

        assert_eq!(0, heap.0.borrow().objects.len());
    }

    #[test]
    fn immutable_with_values() {
        let heap = Heap::default();
        let _heap_guard = push_heap(heap.clone());

        assert_eq!(0, heap.0.borrow().objects.len());

        // immutable values with references are recorded in heap
        Value::from((10, "true"));

        assert_eq!(1, heap.0.borrow().objects.len());
        // object is recorded, but it is already destroyed
        assert!(heap.0.borrow().objects[0].clone().upgrade().is_none());

        // explicitly call GC
        heap.gc("explicit");

        // and the object is gone
        assert_eq!(0, heap.0.borrow().objects.len());
    }

    #[test]
    fn cycle_is_cleared() {
        let heap = Heap::default();
        let _heap_guard = push_heap(heap.clone());

        assert_eq!(0, heap.0.borrow().objects.len());

        let list = Value::from(Vec::<Value>::new());
        // it is cyclic list now
        list.downcast_mut::<List>()
            .unwrap()
            .unwrap()
            .push(list.clone())
            .unwrap();

        assert_eq!(1, heap.0.borrow().objects.len());

        // keep a week reference to test later
        let list = {
            let list = list;
            list.downgrade()
        };

        // heap still contains this object as alive because it references itself
        assert!(heap.0.borrow().objects[0].clone().upgrade().is_some());

        heap.gc("explicit");

        // list is gone
        assert_eq!(0, heap.0.borrow().objects.len());
        // it is actually gone
        assert!(list.upgrade().is_none());
    }
}
