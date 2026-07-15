#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: `from_raw_parts` requires the element memory to be initialized.
#[rapx::verify]
pub fn unsound_from_raw_parts_uninitialized() -> usize {
    let slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_ptr();

    let slice = unsafe { std::slice::from_raw_parts(ptr, 1) };
    slice.len()
}
