#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// With n = 0, !n is 255 for u8 and selects the one-past read.
#[rapx::verify]
pub fn unsound_unsigned_not_selects_out_of_bounds_read(n: u8) -> u8 {
    if n != 0 {
        return 0;
    }
    let data = [7u8];
    let p = data.as_ptr();
    let q = !n;
    unsafe { if q == 255 { p.add(1).read() } else { p.read() } }
}
