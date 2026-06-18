#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the raw pointer is used after the Box reconstructed from it is dropped.
#[rapx::verify]
pub fn unsound_box_from_raw_drop_then_raw_read(value: Box<u32>) -> u32 {
    let raw = Box::into_raw(value);
    let boxed = unsafe { Box::from_raw(raw) };
    drop(boxed);

    unsafe { *raw }
}
