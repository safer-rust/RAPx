#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn unsound_byte_offset_one(data: &[u8]) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        let ptr = base.wrapping_add(1) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}
