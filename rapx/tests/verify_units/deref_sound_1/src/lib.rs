#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Deref(_ptr, u32, _len), kind = "precond")]
unsafe fn require_deref_u32(_ptr: *const u32, _len: usize) {}

// SOUND: the guarded prefix is allocated and in bounds.
#[rapx::verify]
pub fn sound_deref_slice_prefix(data: &[u32], len: usize) {
    if len <= data.len() {
        unsafe {
            require_deref_u32(data.as_ptr(), len);
        }
    }
}
