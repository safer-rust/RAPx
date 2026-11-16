#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unsafe_op_in_unsafe_fn)]

#[inline(never)]
fn identity(p: *mut u8) -> *mut u8 {
    p
}

// Passing null_mut() leaves the identity result null at new_unchecked.
#[rapx::verify]
pub unsafe fn unsound_nullable_identity_result(p: *mut u8) -> core::ptr::NonNull<u8> {
    core::ptr::NonNull::new_unchecked(identity(p))
}
