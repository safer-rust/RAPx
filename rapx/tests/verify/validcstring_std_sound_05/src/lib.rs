#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// SOUND: the input slice is checked to be exactly `b"ok\0"` before the unsafe call.
#[rapx::verify]
pub fn sound_input_slice_exact_match(bytes: &[u8]) -> usize {
    if bytes == b"ok\0" {
        let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(bytes) };
        cstr.to_bytes().len()
    } else {
        0
    }
}
