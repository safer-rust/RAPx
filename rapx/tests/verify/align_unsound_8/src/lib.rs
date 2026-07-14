#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

fn byte_add_as_u32(base: *const u8, offset: usize) -> *const u32 {
    base.wrapping_add(offset) as *const u32
}

#[rapx::verify]
pub fn unsound_helper_with_disjunctive_guard(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 || offset % 4 == 0 {
        let ptr = byte_add_as_u32(base, offset);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}
