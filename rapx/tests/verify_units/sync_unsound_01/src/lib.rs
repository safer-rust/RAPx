#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::cell::UnsafeCell;

// A Cell-like type: `set` mutates through `&self` (interior mutation), so
// `&MyCell` cannot be shared across threads — !Sync.
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
unsafe impl Sync for MyCell {}
