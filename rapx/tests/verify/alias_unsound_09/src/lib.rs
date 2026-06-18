#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ffi::CString;

// UNSOUND: `CString::from_raw` retakes ownership, but the original raw pointer is used afterward.
#[rapx::verify]
pub fn unsound_cstring_from_raw_then_raw_write(input: CString) -> usize {
    let raw = input.into_raw();
    let owned = unsafe { CString::from_raw(raw) };

    unsafe {
        *raw = b'X' as i8;
    }

    owned.as_bytes().len()
}
