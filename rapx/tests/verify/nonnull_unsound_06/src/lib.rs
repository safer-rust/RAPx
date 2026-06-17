#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ptr::NonNull;

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// UNSOUND: `new_unchecked` is called with null, so later `as_ptr` must not hide it.
#[rapx::verify]
pub fn unsound_nonnull_wrapper_from_null() {
    let raw = 0usize as *mut u32;
    let nn = unsafe { NonNull::new_unchecked(raw) };
    let ptr = nn.as_ptr();

    unsafe {
        require_nonnull(ptr);
    }
}
