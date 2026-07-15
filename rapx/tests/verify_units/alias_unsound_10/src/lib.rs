#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::{CStr, c_char};

// UNSOUND: `CStr::from_ptr` creates a shared borrow, then the original pointer mutates it.
#[rapx::verify]
pub fn unsound_cstr_from_ptr_then_raw_mutation(bytes: &mut [u8; 4]) -> usize {
    bytes[0] = b'a';
    bytes[1] = b'b';
    bytes[2] = b'c';
    bytes[3] = 0;

    let ptr = bytes.as_mut_ptr() as *mut c_char;
    let cstr = unsafe { CStr::from_ptr(ptr as *const c_char) };
    unsafe {
        *ptr = b'z' as c_char;
    }
    cstr.to_bytes().len()
}
