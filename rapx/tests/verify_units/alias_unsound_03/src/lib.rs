#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: a mutable slice is created from `Vec` storage, then the original Vec is mutated.
#[rapx::verify]
pub fn unsound_vec_push_while_raw_slice_live(mut data: Vec<u32>) -> u32 {
    let ptr = data.as_mut_ptr();
    let len = data.len();
    let slice = unsafe { std::slice::from_raw_parts_mut(ptr, len) };

    data.push(42);
    if !slice.is_empty() {
        slice[0]
    } else {
        0
    }
}
