#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the returned `'static` slice points into a local Vec that is dropped.
#[rapx::verify]
pub fn static_slice_from_local_vec() -> &'static [u32] {
    let data = vec![1_u32, 2, 3];
    let ptr = data.as_ptr();
    let len = data.len();

    unsafe { std::slice::from_raw_parts(ptr, len) }
}
