#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static LEFT: &[u8] = b"left\0";
static RIGHT: &[u8] = b"right\0";

// SOUND: both branch targets are valid C strings.
#[rapx::verify]
pub fn sound_branch_selects_valid_source(choice: bool) -> usize {
    let ptr = if choice { LEFT.as_ptr() } else { RIGHT.as_ptr() };
    let cstr = unsafe { CStr::from_ptr(ptr as *const c_char) };
    cstr.to_bytes().len()
}
