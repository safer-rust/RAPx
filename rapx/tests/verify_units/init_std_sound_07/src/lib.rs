#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// SOUND: byte 3 is initialized to 33 before it is read.
#[rapx::verify]
pub fn sound_raw_odd_three() -> u8 {
    let mut data = [MaybeUninit::<u8>::uninit(); 8];
    let p = data.as_mut_ptr().cast::<u8>();
    unsafe {
        p.add(1).write(11);
        p.add(3).write(33);
        p.add(5).write(55);
        p.add(7).write(77);
        p.add(3).read()
    }
}
