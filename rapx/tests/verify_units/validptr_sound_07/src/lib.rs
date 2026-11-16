#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// The guard leaves n = 0, whose u8 complement 255 selects the in-bounds read.
#[rapx::verify]
pub fn sound_unsigned_not_selects_in_bounds_read(n: u8) -> u8 {
    if n != 0 {
        return 0;
    }
    let data = [7u8];
    let p = data.as_ptr();
    let q = !n;
    unsafe { if q == 255 { p.read() } else { p.add(1).read() } }
}
