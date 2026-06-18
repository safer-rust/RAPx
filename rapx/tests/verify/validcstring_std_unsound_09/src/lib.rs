#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

static NO_NUL_SUFFIX: &[u8] = b"xxsuffix";

// UNSOUND: pointer arithmetic lands on a suffix that is not NUL-terminated.
#[rapx::verify]
pub fn unsound_from_ptr_suffix_without_nul() -> usize {
    let ptr = unsafe { NO_NUL_SUFFIX.as_ptr().add(2) };
    let cstr = unsafe { CStr::from_ptr(ptr as *const c_char) };
    cstr.to_bytes().len()
}
