#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: the byte string literal is valid UTF-8 (all-ASCII "hello").
#[rapx::verify]
pub fn sound_valid_utf8_literal() -> usize {
    let s = unsafe { std::str::from_utf8_unchecked(b"hello") };
    s.len()
}
