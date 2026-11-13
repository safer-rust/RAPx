#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// Regression for https://github.com/safer-rust/RAPx/issues/336

// The raw write covers bytes [4, 8), but the slice also exposes [8, 12).
#[rapx::verify]
pub fn unsound_raw_write_leaves_second_element_uninitialized() -> usize {
    let mut data = [MaybeUninit::<u32>::uninit(); 3];
    let ptr = unsafe { data.as_mut_ptr().cast::<u32>().add(1) };

    unsafe { ptr.write(7) }; // initializes bytes [4, 8) only
    let slice = unsafe { core::slice::from_raw_parts(ptr, 2) };
    slice[1] as usize // reads uninitialized bytes [8, 12)
}
