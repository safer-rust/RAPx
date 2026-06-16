#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

fn maybe_init_slot(ptr: *mut u32, value: u32, flag: bool) {
    if flag {
        unsafe {
            ptr.write(value);
        }
    }
}

// UNSOUND: the helper may skip initialization before `assume_init_read`.
#[rapx::verify]
pub fn unsound_intra_helper_maybe_initializes(value: u32, flag: bool) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();

    maybe_init_slot(ptr, value, flag);

    unsafe { slot.assume_init_read() }
}
