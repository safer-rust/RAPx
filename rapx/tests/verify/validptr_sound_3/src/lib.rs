#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, _len), kind = "precond")]
unsafe fn require_valid_ptr_u32(_ptr: *const u32, _len: usize) {}

// SOUND: branch guards establish the slice prefix range before the unsafe call.
#[rapx::verify]
pub fn sound_slice_prefix_guarded(data: &[u32], len: usize) {
    if len <= data.len() {
        let ptr = data.as_ptr();

        unsafe {
            require_valid_ptr_u32(ptr, len);
        }
    }
}
