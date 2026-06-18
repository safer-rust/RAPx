#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: `Box::from_raw` owns the allocation, but the original raw pointer is still used.
#[rapx::verify]
pub fn unsound_box_from_raw_then_raw_write(value: Box<u32>) -> u32 {
    let raw = Box::into_raw(value);
    let boxed = unsafe { Box::from_raw(raw) };

    unsafe {
        *raw = 11;
    }

    *boxed
}
