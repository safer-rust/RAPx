#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: ownership is transferred to `Box::from_raw`, and the original pointer is not reused.
#[rapx::verify]
pub fn sound_box_from_raw_consumes_pointer(value: Box<u32>) -> u32 {
    let raw = Box::into_raw(value);
    let boxed = unsafe { Box::from_raw(raw) };
    *boxed
}
