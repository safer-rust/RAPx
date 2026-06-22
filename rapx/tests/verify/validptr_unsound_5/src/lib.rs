#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, _len), kind = "precond")]
unsafe fn require_valid_ptr_u32(_ptr: *const u32, _len: usize) {}

// UNSOUND: start may be negative, so ptr.offset(start) can move before the slice.
#[rapx::verify]
pub fn unsound_signed_suffix_missing_lower_bound(data: &[u32], start: isize, len: usize) {
    let data_len = data.len() as isize;

    if start <= data_len && len <= (data_len - start) as usize {
        let ptr = unsafe { data.as_ptr().offset(start) };

        unsafe {
            require_valid_ptr_u32(ptr, len);
        }
    }
}
