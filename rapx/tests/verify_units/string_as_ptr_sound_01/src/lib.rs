#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `String::as_ptr` (via Deref to `str::as_ptr`) returns a pointer to
// the heap buffer, so dereferencing the first byte is in-bounds.
#[rapx::verify]
pub fn sound_string_as_ptr(s: String) -> u8 {
    let p = s.as_ptr();
    unsafe { *p }
}
