#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::cell::UnsafeCell;

pub struct MyCell {
    value: UnsafeCell<u8>,
}

#[rapx::verify]
unsafe impl Sync for MyCell {}
