#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// Regression for https://github.com/safer-rust/RAPx/issues/335

// Only the first element is initialized.
#[rapx::verify]
pub fn unsound_partial_write_then_read_two(value: u32) -> usize {
    let mut data = [MaybeUninit::<u32>::uninit(); 2];
    data[0].write(value); // initializes bytes [0, 4)

    let ptr = data.as_ptr().cast::<u32>();
    let slice = unsafe { core::slice::from_raw_parts(ptr, 2) };
    slice[1] as usize // reads uninitialized bytes [4, 8)
}
