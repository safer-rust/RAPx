#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// SOUND: the byte slice is a literal C string with one trailing NUL and no interior NUL.
#[rapx::verify]
pub fn sound_literal_bytes_with_nul() -> usize {
    let bytes = b"hello\0";
    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(bytes) };
    cstr.to_bytes().len()
}
