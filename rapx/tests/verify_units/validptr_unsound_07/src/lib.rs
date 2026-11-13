#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// Regression for https://github.com/safer-rust/RAPx/issues/338

// The one-past pointer cannot be dereferenced.
#[rapx::verify]
pub fn unsound_vec_one_past_read() -> u8 {
    let data = vec![7u8];
    let ptr = data.as_ptr();
    unsafe { ptr.add(1).read() }
}
