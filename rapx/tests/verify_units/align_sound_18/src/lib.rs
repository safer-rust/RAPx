#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::align_of;

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn sound_usize_round_trip(data: &[u8]) {
    let base = data.as_ptr();
    let addr = base as usize;

    if addr % align_of::<u32>() == 0 {
        let ptr = addr as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}
