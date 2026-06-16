#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: the write is conditional, but the read is unconditional.
#[rapx::verify]
pub fn unsound_conditional_write_then_assume(value: u32, flag: bool) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();

    if flag {
        slot.write(value);
    }

    unsafe { slot.assume_init_read() }
}
