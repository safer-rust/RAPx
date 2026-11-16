#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// UNSOUND: index == 2 writes byte 5, leaving byte 0 untouched and uninitialized.
#[rapx::verify]
pub fn unsound_symbolic_odd_even_zero(index: usize) -> u8 {
    if index >= 4 {
        return 0;
    }
    let mut data = [MaybeUninit::<u8>::uninit(); 8];
    let p = data.as_mut_ptr().cast::<u8>();
    unsafe {
        p.add(2 * index + 1).write(7);
        p.read()
    }
}
