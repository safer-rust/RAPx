#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CStr;

fn nonzero(byte: u8) -> u8 {
    if byte == 0 { 1 } else { byte }
}

// SOUND: the content is variable, but both interior bytes are normalized to nonzero.
#[rapx::verify]
pub fn sound_variable_bytes_with_guard(a: u8, b: u8) -> usize {
    let bytes = [nonzero(a), nonzero(b), 0];
    let cstr = unsafe { CStr::from_bytes_with_nul_unchecked(&bytes) };
    cstr.to_bytes().len()
}
