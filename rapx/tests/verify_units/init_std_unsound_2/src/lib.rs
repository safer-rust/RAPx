#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// UNSOUND: by-value `assume_init` consumes an uninitialized slot.
#[rapx::verify]
pub fn unsound_assume_init_without_write() -> u32 {
    let slot = MaybeUninit::<u32>::uninit();

    unsafe { slot.assume_init() }
}
