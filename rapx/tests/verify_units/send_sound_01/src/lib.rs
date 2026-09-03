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

// A generic Rc-like type: the value field `T` requires a `T: Send` bound for
// the impl to be sound.
#[rapx::invariant(Owning(ptr))]
#[rapx::invariant(Allocated(ptr))]
pub struct MyRcGeneric<T> {
    ptr: *mut MyRcBoxGeneric<T>,
}

pub struct MyRcBoxGeneric<T> {
    strong: usize,
    value: T,
}

impl<T> MyRcGeneric<T> {
    pub fn inc(&self) {
        unsafe { (*self.ptr).strong += 1 }
    }
}

#[rapx::verify]
unsafe impl<T: Send> Send for MyRcGeneric<T> {}

// A Cell-like type: interior mutability via UnsafeCell, no raw pointer field.
// `set` mutates through `&self` (interior mutation), but the value is still
// Send-safe (move => exclusive).
pub struct MyCell {
    value: UnsafeCell<u8>,
}

impl MyCell {
    pub fn get(&self) -> u8 {
        unsafe { *self.value.get() }
    }

    pub fn set(&self, val: u8) {
        unsafe { *self.value.get() = val }
    }
}

#[rapx::verify]
unsafe impl Send for MyCell {}
