#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// With n = -3, division truncates toward zero to -1 and selects the one-past read.
#[rapx::verify]
pub fn unsound_signed_division_selects_out_of_bounds_read(n: i32) -> u8 {
    if n != -3 {
        return 0;
    }
    let data = [7u8];
    let p = data.as_ptr();
    let q = n / 2;
    unsafe { if q == -1 { p.add(1).read() } else { p.read() } }
}
