#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::rc::Rc;

pub struct RcHolder {
    rc: Rc<u8>,
}

#[rapx::verify]
unsafe impl Send for RcHolder {}

// An Rc-like type: `Clone` copies the raw pointer (aliasing the pointee), so
// the non-atomic `inc` write is a cross-thread data race.
pub struct MyRc {
    ptr: *mut MyRcBox,
}

pub struct MyRcBox {
    strong: usize,
    value: u8,
}

impl Clone for MyRc {
    fn clone(&self) -> Self {
        unsafe { (*self.ptr).strong += 1 }
        MyRc { ptr: self.ptr }
    }
}

impl MyRc {
    pub fn inc(&self) {
        unsafe { (*self.ptr).strong += 1 }
    }
}

#[rapx::verify]
unsafe impl Send for MyRc {}
