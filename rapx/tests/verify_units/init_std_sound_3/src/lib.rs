#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// SOUND: the unsafe read only occurs on the branch that initialized the slot.
#[rapx::verify]
pub fn sound_branch_local_init(value: u32, flag: bool) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();

    if flag {
        slot.write(value);
        unsafe { slot.assume_init_read() }
    } else {
        0
    }
}
