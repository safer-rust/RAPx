#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CString;

fn nonzero(byte: u8) -> u8 {
    if byte == 0 { b'x' } else { byte }
}

// SOUND: Vec contents are variable, but interior bytes are made nonzero and a final NUL is appended.
#[rapx::verify]
pub fn sound_vec_with_nul_from_variables(a: u8, b: u8) -> usize {
    let bytes = vec![nonzero(a), nonzero(b), 0];
    let cstr = unsafe { CString::from_vec_with_nul_unchecked(bytes) };
    cstr.as_bytes().len()
}
