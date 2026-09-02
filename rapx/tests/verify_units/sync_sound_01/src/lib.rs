#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::cell::UnsafeCell;
use std::sync::Mutex;

pub struct MutexCell {
    inner: Mutex<UnsafeCell<u8>>,
}

#[rapx::verify]
unsafe impl Sync for MutexCell {}
