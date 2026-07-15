#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: the bytes were initialized as `u16`, not as `u32` elements.
#[rapx::verify]
pub fn unsound_from_raw_parts_wrong_element_type(value: u16) -> usize {
    let mut slot = MaybeUninit::<u16>::uninit();
    slot.write(value);

    let ptr = slot.as_ptr();
    let slice = unsafe { std::slice::from_raw_parts(ptr as *const u32, 1) };
    slice.len()
}
