#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(Align(_ptr, T), kind = "precond")]
unsafe fn require_align<T>(_ptr: *const T) {}

// UNSOUND: `&[u8]` is only 1-byte aligned, while an unconstrained `T` may
// require a larger alignment (e.g. `u64`).  The old `align = 1` fallback for
// a generic `T` used to discharge this as SOUND.
#[rapx::verify]
pub fn unsound_unbounded_generic_cross_cast<T>(data: &[u8]) {
    let ptr = data.as_ptr() as *const T;

    unsafe {
        require_align::<T>(ptr);
    }
}

#[rapx::requires(Align(_ptr, u64), kind = "precond")]
unsafe fn require_u64_alignment(_ptr: *const u64) {}

#[rapx::verify]
pub fn unsound_vec_u8_buffer_alignment() {
    let mut bytes = vec![0u8; 16];
    unsafe { require_u64_alignment(bytes.as_mut_ptr().cast::<u64>()) }
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_u32_alignment(_ptr: *const u32) {}

#[inline(never)]
fn offset_on_wide_const(value: u128, ptr: *const u32) -> *const u32 {
    if value == 0 {
        ptr
    } else {
        ptr.cast::<u8>().wrapping_add(1).cast::<u32>()
    }
}

#[rapx::verify]
pub fn unsound_wide_call_argument(data: &[u32]) {
    let ptr = offset_on_wide_const(18446744073709551616u128, data.as_ptr());
    unsafe { require_u32_alignment(ptr) }
}

#[inline(never)]
fn aligned_on_wide_const(value: u128, ptr: *const u32) -> *const u32 {
    if value == 0 {
        ptr.cast::<u8>().wrapping_add(1).cast::<u32>()
    } else {
        ptr
    }
}

#[rapx::verify]
pub fn sound_wide_call_argument(data: &[u32]) {
    let ptr = aligned_on_wide_const(18446744073709551616u128, data.as_ptr());
    unsafe { require_u32_alignment(ptr) }
}
