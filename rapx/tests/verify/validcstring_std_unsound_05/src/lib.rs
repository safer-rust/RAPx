#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// UNSOUND: the input slice only checks the final NUL, not the absence of interior NUL bytes.
#[rapx::verify]
pub fn unsound_input_slice_only_checks_last_nul(bytes: &[u8]) -> usize {
    if bytes.len() >= 2 && bytes[bytes.len() - 1] == 0 {
        let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(bytes) };
        cstr.to_bytes().len()
    } else {
        0
    }
}
