#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// SOUND: the loop uses `len` as its bound and writes the whole slice prefix.
#[rapx::verify]
pub fn sound_len_bound_loop_initializes_slice(value: u32) -> usize {
    let mut data = [MaybeUninit::<u32>::uninit(); 2];
    let len = 2;
    let mut i = 0;

    loop {
        if i >= len {
            break;
        }
        if i == 0 {
            data[0].write(value);
        } else {
            data[1].write(value + 1);
        }
        i += 1;
    }

    let ptr = data.as_ptr() as *const u32;
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    slice.len()
}
