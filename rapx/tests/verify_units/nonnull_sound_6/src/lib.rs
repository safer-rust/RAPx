#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::ptr::NonNull;

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// SOUND: `NonNull::from` is built from a reference and `as_ptr` preserves non-nullness.
#[rapx::verify]
pub fn sound_nonnull_wrapper_from_ref() {
    let value = 23_u32;
    let ptr = NonNull::from(&value).as_ptr();

    unsafe {
        require_nonnull(ptr);
    }
}
