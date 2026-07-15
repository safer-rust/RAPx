#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn sound_add_sub_chain(data: &[u8], add_a: usize, sub_b: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && add_a % 4 == 0 && sub_b % 4 == 0 {
        let ptr = base.wrapping_add(add_a).wrapping_sub(sub_b) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}
