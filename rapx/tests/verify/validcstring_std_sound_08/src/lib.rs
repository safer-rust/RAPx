#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static PREFIXED: &[u8] = b"xxsuffix\0";

// SOUND: pointer arithmetic skips a non-C-string prefix and lands on a valid suffix.
#[rapx::verify]
pub fn sound_from_ptr_suffix_after_add() -> usize {
    let ptr = unsafe { PREFIXED.as_ptr().add(2) };
    let cstr = unsafe { CStr::from_ptr(ptr as *const c_char) };
    cstr.to_bytes().len()
}
