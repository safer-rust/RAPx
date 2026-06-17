#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: an empty slice does not allocate one readable u32 element.
#[rapx::verify]
pub fn unsound_empty_slice_needs_one_element(data: &[u32]) {
    if data.is_empty() {
        let ptr = data.as_ptr();

        unsafe {
            require_allocated_u32(ptr);
        }
    }
}
