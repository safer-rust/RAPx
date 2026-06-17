#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// UNSOUND: the guard proves only an unrelated pointer is non-null.
#[rapx::verify]
pub unsafe fn unsound_unrelated_guard(ptr: *const u32) {
    let value = 29_u32;
    let guard = &value as *const u32;

    if (guard as usize) != 0 {
        unsafe {
            require_nonnull(ptr);
        }
    }
}
