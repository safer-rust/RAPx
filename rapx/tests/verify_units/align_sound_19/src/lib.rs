#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::verify]
pub fn sound_usize_add_guarded(data: &[u8], offset: usize) {
    let base = data.as_ptr();
    let addr = base as usize;

    if addr % 4 == 0 && offset % 4 == 0 {
        let ptr = (addr + offset) as *const u32;
        unsafe {
            require_align_u32(ptr);
        }
    }
}
