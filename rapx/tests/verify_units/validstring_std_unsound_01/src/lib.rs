#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: the byte string literal is not valid UTF-8 (0xFF / 0xFE are invalid
// lead bytes).
#[rapx::verify]
pub fn unsound_invalid_utf8_literal() -> usize {
    let s = unsafe { std::str::from_utf8_unchecked(b"\xFF\xFE") };
    s.len()
}
