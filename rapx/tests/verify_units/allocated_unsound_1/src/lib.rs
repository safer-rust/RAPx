#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

// UNSOUND: a null pointer is not backed by any allocation.
#[rapx::verify]
pub fn unsound_null_not_allocated() {
    let ptr = std::ptr::null::<u32>();

    unsafe {
        require_allocated_u32(ptr);
    }
}
