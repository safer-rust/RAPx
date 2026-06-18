#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static MISSING_NUL: &[u8] = b"not-terminated";

// UNSOUND: `from_ptr` may scan past the object because the static byte string has no NUL.
#[rapx::verify]
pub fn unsound_static_from_ptr_without_nul() -> usize {
    let ptr = MISSING_NUL.as_ptr() as *const c_char;
    let cstr = unsafe { CStr::from_ptr(ptr) };
    cstr.to_bytes().len()
}
