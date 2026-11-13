#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// Regression for https://github.com/safer-rust/RAPx/issues/336

// With index == 0, data[1] remains uninitialized.
#[rapx::verify]
pub fn unsound_symbolic_write_leaves_other_element_uninitialized(index: usize) -> u8 {
    let mut data = [MaybeUninit::<u8>::uninit(); 2];
    data[index].write(7);

    let ptr = data.as_ptr().cast::<u8>();
    let slice = unsafe { core::slice::from_raw_parts(ptr, 2) };
    slice[1]
}
