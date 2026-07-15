#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u32) {}

// SOUND: both branches derive the pointer from `slice.as_ptr()`.
#[rapx::verify]
pub fn sound_slice_as_ptr_branch(data: &[u32], choose_base: bool) {
    let base = data.as_ptr();
    let ptr = if choose_base {
        base
    } else {
        base.wrapping_add(0)
    };

    unsafe {
        require_nonnull(ptr);
    }
}
