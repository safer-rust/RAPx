#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// UNSOUND: the byte slice has an interior NUL before the trailing NUL.
#[rapx::verify]
pub fn unsound_bytes_with_interior_nul() -> usize {
    let bytes = b"he\0llo\0";
    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(bytes) };
    cstr.to_bytes().len()
}
