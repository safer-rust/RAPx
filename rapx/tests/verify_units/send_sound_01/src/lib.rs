#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::cell::UnsafeCell;

#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct ReadOnlyPtr {
    ptr: *const u8,
}

#[rapx::verify]
unsafe impl Send for ReadOnlyPtr {}

// A `*mut` field written through exclusively (no `Clone` => no aliasing): the
// write is not a cross-thread data race, so Send-safe.
#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct MyRc {
    ptr: *mut MyRcBox,
}

pub struct MyRcBox {
    strong: usize,
    value: u8,
}

impl MyRc {
    pub fn inc(&self) {
        unsafe { (*self.ptr).strong += 1 }
    }
}

#[rapx::verify]
unsafe impl Send for MyRc {}

pub struct MyCell {
    value: UnsafeCell<u8>,
}

#[rapx::verify]
unsafe impl Send for MyCell {}
