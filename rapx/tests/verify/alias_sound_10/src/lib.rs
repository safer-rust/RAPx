#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CString;

// SOUND: CString::from_raw retakes ownership and the original raw pointer is not reused.
#[rapx::verify]
pub fn sound_cstring_from_raw_no_reuse(input: CString) -> usize {
    let raw = input.into_raw();
    let owned = unsafe { CString::from_raw(raw) };
    owned.as_bytes().len()
}
