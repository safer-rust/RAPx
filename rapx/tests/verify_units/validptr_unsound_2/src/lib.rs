#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidPtr(_ptr, u32, 1), kind = "precond")]
unsafe fn require_valid_ptr_one(_ptr: *const u32) {}

// UNSOUND: the one-past pointer is allocated as provenance but not dereferenceable.
#[rapx::verify]
pub fn unsound_one_past_requires_one_element(data: &[u32]) {
    let ptr = unsafe { data.as_ptr().add(data.len()) };

    unsafe {
        require_valid_ptr_one(ptr);
    }
}
