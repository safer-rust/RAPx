#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CString;

// UNSOUND: `a` or `b` can be zero, creating an interior NUL before the final NUL.
#[rapx::verify]
pub fn unsound_vec_with_variable_interior_nul(a: u8, b: u8) -> usize {
    let bytes = vec![a, b, 0];
    let cstr = unsafe { CString::from_vec_with_nul_unchecked(bytes) };
    cstr.as_bytes().len()
}
