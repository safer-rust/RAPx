#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

fn build_slice<'a>(ptr: *const u32, len: usize) -> &'a [u32] {
    unsafe { std::slice::from_raw_parts(ptr, len) }
}

// SOUND: the helper creates a shared slice, and the caller only reads through it.
#[rapx::verify]
pub fn sound_helper_shared_slice(data: &[u32]) -> u32 {
    let ptr = data.as_ptr();
    let slice = build_slice(ptr, data.len());
    slice.iter().copied().next().unwrap_or(0)
}
