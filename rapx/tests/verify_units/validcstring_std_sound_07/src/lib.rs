#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

// SOUND: the loop writes only nonzero bytes before writing the final NUL terminator.
#[rapx::verify]
pub fn sound_loop_builds_valid_c_string(seed: u8) -> usize {
    let mut bytes = [0_u8; 5];
    let mut i = 0;

    while i < bytes.len() {
        if i == bytes.len() - 1 {
            bytes[i] = 0;
        } else if seed == 0 {
            bytes[i] = b'a';
        } else {
            bytes[i] = seed;
        }
        i += 1;
    }

    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(&bytes) };
    cstr.to_bytes().len()
}
