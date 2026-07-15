#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: Vec::from_raw_parts retakes ownership, but the original raw pointer is reused.
#[rapx::verify]
pub fn unsound_vec_from_raw_parts_then_raw_write(mut data: Vec<u32>) -> u32 {
    let ptr = data.as_mut_ptr();
    let len = data.len();
    let cap = data.capacity();
    std::mem::forget(data);

    let owned = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    unsafe {
        *ptr = 41;
    }
    owned.first().copied().unwrap_or(0)
}
