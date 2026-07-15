#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the length is too large for the `size_of::<u32>() * len` bound.
#[rapx::verify]
pub fn unsound_std_from_raw_parts_validnum_overflow() -> usize {
    let data = [1_u32, 2_u32];
    let ptr = data.as_ptr();
    let slice = unsafe { std::slice::from_raw_parts(ptr, usize::MAX) };
    slice.len()
}
