#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[inline(never)]
fn identity(p: *mut u8) -> *mut u8 {
    p
}

// A pointer from &mut u8 stays non-null through the identity call.
#[rapx::verify]
pub fn sound_nonnull_identity_result(value: &mut u8) -> core::ptr::NonNull<u8> {
    let p = value as *mut u8;
    unsafe { core::ptr::NonNull::new_unchecked(identity(p)) }
}
