#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// SOUND: `write` initializes the slot before `assume_init_read` observes it.
#[rapx::verify]
pub fn sound_assume_init_read_after_write(value: u32) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    slot.write(value);

    unsafe { slot.assume_init_read() }
}
