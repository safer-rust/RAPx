#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::mem::MaybeUninit;

// Regression for https://github.com/safer-rust/RAPx/issues/335

#[repr(C)]
struct PrefixAndHole {
    prefix: [u8; 4096],
    hole: MaybeUninit<u8>,
}

// The final byte of the aggregate is uninitialized.
#[rapx::verify]
pub fn unsound_initialized_prefix_with_one_byte_hole() -> usize {
    let data = PrefixAndHole {
        prefix: [0; 4096],
        hole: MaybeUninit::uninit(),
    };

    let ptr = core::ptr::addr_of!(data).cast::<u8>();
    let slice = unsafe { core::slice::from_raw_parts(ptr, 4097) };
    slice[4096] as usize
}
