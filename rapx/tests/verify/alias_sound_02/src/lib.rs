#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: the mutable slice's lifetime ends before the original raw pointer is used again.
#[rapx::verify]
pub fn sound_raw_use_after_slice_scope(data: &mut [u32]) -> u32 {
    let ptr = data.as_mut_ptr();
    let len = data.len();

    {
        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, len) };
        if !slice.is_empty() {
            slice[0] = 1;
        }
    }

    unsafe {
        if len > 0 {
            *ptr
        } else {
            0
        }
    }
}
