#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::rc::Rc;

pub struct RcHolder {
    rc: Rc<u8>,
}

#[rapx::verify]
unsafe impl Send for RcHolder {}

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
