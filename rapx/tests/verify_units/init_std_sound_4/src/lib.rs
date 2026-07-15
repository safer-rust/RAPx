#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

fn init_slot(ptr: *mut u32, value: u32) {
    unsafe {
        ptr.write(value);
    }
}

// SOUND: the intra-procedural callee always initializes the pointee before use.
#[rapx::verify]
pub fn sound_intra_helper_initializes(value: u32) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();

    init_slot(ptr, value);

    unsafe { slot.assume_init_read() }
}
