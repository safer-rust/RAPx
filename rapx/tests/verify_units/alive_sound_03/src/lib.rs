#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: the returned lifetime is explicitly tied to the source slice.
#[rapx::verify]
pub fn slice_from_host<'a>(host: &'a [u32]) -> &'a [u32] {
    unsafe { std::slice::from_raw_parts(host.as_ptr(), host.len()) }
}
