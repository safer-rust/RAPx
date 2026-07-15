#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, _len), kind = "precond")]
unsafe fn require_valid_ptr_u32(_ptr: *const u32, _len: usize) {}

// SOUND: signed start is lower-bounded and the remaining slice length covers len.
#[rapx::verify]
pub fn sound_signed_suffix_guarded(data: &[u32], start: isize, len: usize) {
    let data_len = data.len() as isize;

    if 0 <= start && start <= data_len && len <= (data_len - start) as usize {
        let ptr = unsafe { data.as_ptr().offset(start) };

        unsafe {
            require_valid_ptr_u32(ptr, len);
        }
    }
}
