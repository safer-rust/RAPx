#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the original raw pointer is used while a mutable slice alias is live.
#[rapx::verify]
pub fn unsound_mut_slice_then_raw_read(data: &mut [u32]) -> u32 {
    let ptr = data.as_mut_ptr();
    let slice = unsafe { std::slice::from_raw_parts_mut(ptr, data.len()) };

    if !slice.is_empty() {
        slice[0] = 1;
        let read_back = unsafe { *ptr };
        slice[0] + read_back
    } else {
        0
    }
}
