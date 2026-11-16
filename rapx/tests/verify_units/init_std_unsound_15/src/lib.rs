#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// UNSOUND: odd-byte writes leave byte 2 untouched and uninitialized.
#[rapx::verify]
pub fn unsound_raw_even_two() -> u8 {
    let mut data = [MaybeUninit::<u8>::uninit(); 8];
    let p = data.as_mut_ptr().cast::<u8>();
    unsafe {
        p.add(1).write(11);
        p.add(3).write(33);
        p.add(5).write(55);
        p.add(7).write(77);
        p.add(2).read()
    }
}
