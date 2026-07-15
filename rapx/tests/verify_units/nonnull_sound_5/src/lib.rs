#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// SOUND: a raw pointer argument is guarded by a non-zero address check.
#[rapx::verify]
pub unsafe fn sound_raw_arg_guarded(ptr: *const u32) {
    if (ptr as usize) != 0 {
        unsafe {
            require_nonnull(ptr);
        }
    }
}
