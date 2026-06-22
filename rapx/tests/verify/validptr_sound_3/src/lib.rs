#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, _len), kind = "precond")]
unsafe fn require_valid_ptr_u32(_ptr: *const u32, _len: usize) {}

// SOUND: branch guards establish the slice suffix range before the unsafe call.
#[rapx::verify]
pub fn sound_slice_suffix_guarded(data: &[u32], start: usize, len: usize) {
    if start <= data.len() && len <= data.len() - start {
        let ptr = unsafe { data.as_ptr().add(start) };

        unsafe {
            require_valid_ptr_u32(ptr, len);
        }
    }
}
