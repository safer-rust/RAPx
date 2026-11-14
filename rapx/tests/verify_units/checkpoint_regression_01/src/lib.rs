#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

use std::sync::atomic::{AtomicUsize, Ordering};

static mut FIRST: u8 = 0;
static mut SECOND: u64 = 0;

#[rapx::verify]
pub unsafe fn two_static_mut_accesses() {
    let first = &raw mut FIRST;
    let second = &raw mut SECOND;
    unsafe { *first = 1 };
    unsafe { *second = 2 };
}

/// The later assignment cannot make the earlier one-past dereference valid.
#[rapx::verify]
pub unsafe fn deref_before_reassign() -> u8 {
    let bytes = [7u8];
    let base = bytes.as_ptr();
    let mut ptr = base.wrapping_add(1);
    let value = unsafe { *ptr };
    ptr = base;
    std::hint::black_box(ptr);
    value
}

#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Alias(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct PlainWriteWithAtomicRead {
    ptr: *mut usize,
    counter: AtomicUsize,
}

impl Clone for PlainWriteWithAtomicRead {
    fn clone(&self) -> Self {
        self.update();
        Self {
            ptr: self.ptr,
            counter: AtomicUsize::new(0),
        }
    }
}

impl PlainWriteWithAtomicRead {
    pub fn update(&self) {
        let _ = self.counter.load(Ordering::SeqCst);
        unsafe { *self.ptr = 1 };
    }
}

#[rapx::verify]
unsafe impl Send for PlainWriteWithAtomicRead {}

#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Alias(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct PlainWriteWithAtomicUpdate {
    ptr: *mut usize,
    counter: AtomicUsize,
}

impl Clone for PlainWriteWithAtomicUpdate {
    fn clone(&self) -> Self {
        self.update();
        Self {
            ptr: self.ptr,
            counter: AtomicUsize::new(0),
        }
    }
}

impl PlainWriteWithAtomicUpdate {
    pub fn update(&self) {
        self.counter.fetch_add(1, Ordering::SeqCst);
        unsafe { *self.ptr = 1 };
    }
}

#[rapx::verify]
unsafe impl Send for PlainWriteWithAtomicUpdate {}
