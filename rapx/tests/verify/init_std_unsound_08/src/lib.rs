#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: even indices are exposed by `from_raw_parts` but never initialized.
#[rapx::verify]
pub fn unsound_len_bound_loop_skips_even_indices(value: u32) -> usize {
    let mut data = [MaybeUninit::<u32>::uninit(); 2];
    let len = 2;
    let mut i = 0;

    loop {
        if i >= len {
            break;
        }
        if i % 2 == 1 {
            data[1].write(value);
        }
        i += 1;
    }

    let ptr = data.as_ptr() as *const u32;
    let slice = unsafe { std::slice::from_raw_parts(ptr, len) };
    slice.len()
}
