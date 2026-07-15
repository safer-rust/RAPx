#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// UNSOUND: the loop may write an interior NUL while still writing a trailing NUL.
#[rapx::verify]
pub fn unsound_loop_writes_interior_nul(flag: bool) -> usize {
    let mut bytes = [b'a'; 4];
    let mut i = 0;

    while i < bytes.len() {
        if i == 1 && flag {
            bytes[i] = 0;
        } else if i == bytes.len() - 1 {
            bytes[i] = 0;
        } else {
            bytes[i] = b'x';
        }
        i += 1;
    }

    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(&bytes) };
    cstr.to_bytes().len()
}
