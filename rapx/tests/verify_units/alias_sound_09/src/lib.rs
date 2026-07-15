#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: ownership is temporarily moved into Box and then explicitly returned with `into_raw`.
#[rapx::verify]
pub fn sound_box_from_raw_then_into_raw(value: Box<u32>) -> u32 {
    let raw = Box::into_raw(value);
    let boxed = unsafe { Box::from_raw(raw) };
    let raw_again = Box::into_raw(boxed);

    let value = unsafe { *raw_again };
    unsafe {
        drop(Box::from_raw(raw_again));
    }
    value
}
