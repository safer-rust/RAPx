#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// UNSOUND: a raw pointer argument is not non-null by type alone.
#[rapx::verify]
pub unsafe fn unsound_raw_pointer_argument(ptr: *const u32) {
    unsafe {
        require_nonnull(ptr);
    }
}
