#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::sync::atomic::{AtomicUsize, Ordering};

// An `Arc`-like type: a raw pointer plus an atomic reference count.  `Clone`
// copies the raw pointer (aliasing the pointee), but the shared state is only
// mutated through `AtomicUsize::fetch_add`, so the aliased updates are atomic
// and therefore Send-safe.
#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct MyArc {
    ptr: *mut MyArcInner,
}

pub struct MyArcInner {
    strong: AtomicUsize,
    value: u8,
}

impl Clone for MyArc {
    fn clone(&self) -> Self {
        self.inc();
        MyArc { ptr: self.ptr }
    }
}

impl MyArc {
    pub fn inc(&self) {
        unsafe {
            (*self.ptr).strong.fetch_add(1, Ordering::SeqCst);
        }
    }
}

#[rapx::verify]
unsafe impl Send for MyArc {}
