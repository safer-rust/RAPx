#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// Passing set_null overwrites the pointer before the read.
#[rapx::verify]
pub fn unsound_callback_write_invalidates_pointer(callback: fn(&mut *const u8)) -> u8 {
    let data = [7u8];
    let mut p = data.as_ptr();
    callback(&mut p);
    unsafe { p.read() }
}

pub fn set_null(p: &mut *const u8) {
    *p = core::ptr::null();
}
