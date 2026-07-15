#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, _len), kind = "precond")]
unsafe fn require_valid_ptr_u32(_ptr: *const u32, _len: usize) {}

// UNSOUND: the requested length is one element larger than the allocation.
#[rapx::verify]
pub fn unsound_stack_array_len_too_large() {
    let data = [1_u32, 2, 3, 4];

    unsafe {
        require_valid_ptr_u32(data.as_ptr(), data.len() + 1);
    }
}
