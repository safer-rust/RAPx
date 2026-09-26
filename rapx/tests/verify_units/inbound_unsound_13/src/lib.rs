#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: `i` is 100 whenever `a & 1 == 0`. The twelve `if`s after it give
// 8192 paths, past the whole-CFG path limit, so the paths through the
// out-of-bounds side are never enumerated.
#[rapx::verify]
pub fn unsound_index_past_path_limit(a: u32) -> u8 {
    let arr = [0u8; 4];
    let mut k = a;
    let i = if a & 1 != 0 { 0 } else { 100 };
    if a & 2 != 0 {
        k = k.wrapping_mul(3);
    }
    if a & 4 != 0 {
        k = k.wrapping_mul(4);
    }
    if a & 8 != 0 {
        k = k.wrapping_mul(5);
    }
    if a & 16 != 0 {
        k = k.wrapping_mul(6);
    }
    if a & 32 != 0 {
        k = k.wrapping_mul(7);
    }
    if a & 64 != 0 {
        k = k.wrapping_mul(8);
    }
    if a & 128 != 0 {
        k = k.wrapping_mul(9);
    }
    if a & 256 != 0 {
        k = k.wrapping_mul(10);
    }
    if a & 512 != 0 {
        k = k.wrapping_mul(11);
    }
    if a & 1024 != 0 {
        k = k.wrapping_mul(12);
    }
    if a & 2048 != 0 {
        k = k.wrapping_mul(13);
    }
    if a & 4096 != 0 {
        k = k.wrapping_mul(14);
    }
    unsafe { *arr.get_unchecked(i) }.wrapping_add(k as u8)
}
