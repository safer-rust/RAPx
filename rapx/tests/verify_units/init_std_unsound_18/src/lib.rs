#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// UNSOUND: the loop initializes only odd bytes, leaving byte 0 untouched.
#[rapx::verify]
pub fn unsound_loop_odd_even_zero() -> u8 {
    let mut data = [MaybeUninit::<u8>::uninit(); 8];
    let p = data.as_mut_ptr().cast::<u8>();
    let mut i = 1usize;
    while i < 8 {
        unsafe {
            p.add(i).write(7);
        }
        i += 2;
    }
    unsafe { p.read() }
}
