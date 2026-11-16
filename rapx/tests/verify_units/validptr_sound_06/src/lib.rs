#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// The guard leaves n = -3, whose quotient -1 selects the in-bounds read.
#[rapx::verify]
pub fn sound_signed_division_selects_in_bounds_read(n: i32) -> u8 {
    if n != -3 {
        return 0;
    }
    let data = [7u8];
    let p = data.as_ptr();
    let q = n / 2;
    unsafe { if q == -1 { p.read() } else { p.add(1).read() } }
}
