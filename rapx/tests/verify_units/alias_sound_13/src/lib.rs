#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

/// SOUND: `&mut u16` → `from_raw_parts_mut` → `&mut [u8]`.
#[rapx::verify]
pub fn as_bytes_mut_sound(x: &mut u16) -> &mut [u8] {
    unsafe { slice::from_raw_parts_mut(x as *mut u16 as *mut u8, mem::size_of::<u16>()) }
}
