#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: the Vec may reallocate before the raw-derived slice is created, not while it is live.
#[rapx::verify]
pub fn sound_vec_reserve_before_raw_slice(mut data: Vec<u32>) -> u32 {
    data.reserve(8);
    let ptr = data.as_mut_ptr();
    let len = data.len();
    let slice = unsafe { std::slice::from_raw_parts_mut(ptr, len) };

    if !slice.is_empty() {
        slice[0] = 5;
        slice[0]
    } else {
        0
    }
}
