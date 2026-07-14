#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

fn byte_add_as_u32(base: *const u8, offset: usize) -> *const u32 {
    base.wrapping_add(offset) as *const u32
}

fn hop2(base: *const u8, offset: usize) -> *const u32 {
    byte_add_as_u32(base, offset)
}

fn hop1(base: *const u8, offset: usize) -> *const u32 {
    hop2(base, offset)
}

#[rapx::verify]
pub fn unsound_multi_hop_missing_offset_guard(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        let ptr = hop1(base, offset);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}
