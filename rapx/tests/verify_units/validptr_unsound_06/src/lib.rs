#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// Regression for https://github.com/safer-rust/RAPx/issues/337

// 256_u16 as u8 is zero, selecting the out-of-bounds read.
#[rapx::verify]
pub fn unsound_narrow_cast_selects_out_of_bounds_read() -> u8 {
    let source: u16 = 256;
    let offset = source as u8;
    let data = [7u8; 1];
    let ptr = data.as_ptr();

    unsafe {
        if offset == 0 {
            ptr.add(1).read()
        } else {
            ptr.read()
        }
    }
}
