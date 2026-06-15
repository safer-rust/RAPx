#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_ptr_add_inbound(_ptr: *const u32) {}

// UNSOUND: simulates `ptr.add(index)` without proving `index < data.len()`.
#[rapx::verify]
pub fn unsound_ptr_add_without_guard(data: &[u32], index: usize) {
    let ptr = data.as_ptr();
    let current = unsafe { ptr.add(index) };

    unsafe {
        require_ptr_add_inbound(current);
    }
}
