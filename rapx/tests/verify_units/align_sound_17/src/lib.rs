#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn sound_offset_zero_preserves_align(data: &[u32]) {
    let ptr = data.as_ptr();
    let shifted = ptr.wrapping_offset(0);

    unsafe {
        require_align_u32(shifted);
    }
}
