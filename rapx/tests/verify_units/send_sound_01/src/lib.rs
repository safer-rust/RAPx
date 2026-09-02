#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::cell::UnsafeCell;

pub struct PlainData {
    value: u8,
}

#[rapx::verify]
unsafe impl Send for PlainData {}

pub struct ReadOnlyPtr {
    ptr: *const u8,
}

#[rapx::verify]
unsafe impl Send for ReadOnlyPtr {}

// A `*mut` field with no method that writes through it: structurally mutable
// but behaviourally read-only, so Send-safe.
pub struct MutablePtrNoWrite {
    ptr: *mut u8,
}

#[rapx::verify]
unsafe impl Send for MutablePtrNoWrite {}

pub struct MyCell {
    value: UnsafeCell<u8>,
}

#[rapx::verify]
unsafe impl Send for MyCell {}
