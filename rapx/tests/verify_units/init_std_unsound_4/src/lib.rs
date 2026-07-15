#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: initializing `other` does not initialize `slot`.
#[rapx::verify]
pub fn unsound_write_different_slot(value: u32) -> u32 {
    let slot = MaybeUninit::<u32>::uninit();
    let mut other = MaybeUninit::<u32>::uninit();

    other.write(value);

    unsafe { slot.assume_init_read() }
}
