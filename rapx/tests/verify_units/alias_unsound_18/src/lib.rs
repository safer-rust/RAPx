#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

/// UNSOUND: `&u16` → `from_raw_parts_mut` → `&mut [u8]`, shared→mutable.
#[rapx::verify]
pub fn as_bytes_mut_unsound(x: &u16) -> &mut [u8] {
    unsafe { slice::from_raw_parts_mut(x as *const u16 as *mut u8, mem::size_of::<u16>()) }
}
