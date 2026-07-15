#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::size_of;

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn sound_usize_mul_div_offset(data: &[u8], units: usize) {
    let base = data.as_ptr();
    let addr = base as usize;
    let offset = (units * size_of::<u64>()) / 2;

    if addr % 4 == 0 {
        let ptr = (addr + offset) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}
