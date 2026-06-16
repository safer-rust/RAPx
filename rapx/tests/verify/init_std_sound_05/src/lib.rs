#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// SOUND: the SCC writes the slot before `from_raw_parts` exposes it as a slice.
#[rapx::verify]
pub fn sound_loop_initializes_slice(value: u32) -> usize {
    let mut slot = MaybeUninit::<u32>::uninit();
    let mut done = false;

    loop {
        slot.write(value);
        if done {
            break;
        }
        done = true;
    }

    let ptr = slot.as_ptr();
    let slice = unsafe { std::slice::from_raw_parts(ptr, 1) };
    slice.len()
}
