#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the output lifetime is tied to `host`, but the pointer may come from elsewhere.
#[rapx::verify]
pub fn slice_tied_to_unrelated_host<'a>(
    host: &'a [u32],
    ptr: *const u32,
    len: usize,
) -> &'a [u32] {
    let _ = host;
    unsafe { std::slice::from_raw_parts(ptr, len) }
}
