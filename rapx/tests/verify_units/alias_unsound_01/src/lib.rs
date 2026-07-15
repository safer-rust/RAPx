#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the raw pointer mutates memory while a shared slice from the same pointer is live.
#[rapx::verify]
pub fn unsound_shared_slice_then_raw_write(data: &mut [u32]) -> u32 {
    let ptr = data.as_mut_ptr();
    let slice = unsafe { std::slice::from_raw_parts(ptr, data.len()) };

    if !slice.is_empty() {
        unsafe {
            *ptr = 9;
        }
        slice[0]
    } else {
        0
    }
}
