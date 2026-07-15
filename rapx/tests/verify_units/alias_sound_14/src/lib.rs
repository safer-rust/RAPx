#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem;
use std::slice;

/// SOUND: `&u16` → `from_raw_parts` → `&[u8]`.
#[rapx::verify]
pub fn as_bytes_sound(x: &u16) -> &[u8] {
    unsafe { slice::from_raw_parts(x as *const u16 as *const u8, mem::size_of::<u16>()) }
}
