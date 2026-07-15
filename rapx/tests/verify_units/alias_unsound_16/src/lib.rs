#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: reserving the Vec while a raw-derived mutable slice is live may invalidate the slice.
#[rapx::verify]
pub fn unsound_vec_reserve_while_raw_slice_live(mut data: Vec<u32>) -> u32 {
    let ptr = data.as_mut_ptr();
    let len = data.len();
    let slice = unsafe { std::slice::from_raw_parts_mut(ptr, len) };

    data.reserve(1024);
    if !slice.is_empty() {
        slice[0]
    } else {
        0
    }
}
