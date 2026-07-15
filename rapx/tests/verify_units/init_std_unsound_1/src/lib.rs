#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: `assume_init_read` reads a slot that was never initialized.
#[rapx::verify]
pub fn unsound_assume_init_read_without_write() -> u32 {
    let slot = MaybeUninit::<u32>::uninit();

    unsafe { slot.assume_init_read() }
}
