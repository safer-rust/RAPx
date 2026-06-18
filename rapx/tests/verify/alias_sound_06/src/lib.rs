#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static NAME: &[u8] = b"alias-ok\0";

// SOUND: `CStr::from_ptr` borrows the C string, and the original pointer is not used to mutate it.
#[rapx::verify]
pub fn sound_cstr_from_ptr_read_only() -> usize {
    let ptr = NAME.as_ptr() as *const c_char;
    let cstr = unsafe { CStr::from_ptr(ptr) };
    cstr.to_bytes().len()
}
