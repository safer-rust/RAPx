#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static VALID: &[u8] = b"static-name\0";

// SOUND: `from_ptr` starts from a static NUL-terminated byte string.
#[rapx::verify]
pub fn sound_static_from_ptr() -> usize {
    let ptr = VALID.as_ptr() as *const c_char;
    let cstr = unsafe { CStr::from_ptr(ptr) };
    cstr.to_bytes().len()
}
