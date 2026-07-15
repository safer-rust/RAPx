#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static GOOD: &[u8] = b"good\0";
static BAD: &[u8] = b"bad";

// UNSOUND: one branch can select a non-terminated byte string.
#[rapx::verify]
pub fn unsound_branch_mixes_valid_and_invalid(choice: bool) -> usize {
    let ptr = if choice { GOOD.as_ptr() } else { BAD.as_ptr() };
    let cstr = unsafe { CStr::from_ptr(ptr as *const c_char) };
    cstr.to_bytes().len()
}
