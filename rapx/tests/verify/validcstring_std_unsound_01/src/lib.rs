#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// UNSOUND: the byte slice has no trailing NUL terminator.
#[rapx::verify]
pub fn unsound_bytes_without_nul() -> usize {
    let bytes = b"hello";
    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(bytes) };
    cstr.to_bytes().len()
}
