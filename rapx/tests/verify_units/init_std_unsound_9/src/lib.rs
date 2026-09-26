#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

// Writes `out` only when `a & 1 != 0`. The twelve `if`s after it give 4096
// paths on the writing side alone, so a must-write summary over the first
// enumerated paths never sees the side that skips the write.
fn maybe_init(out: &mut MaybeUninit<u32>, a: u32) -> u32 {
    let mut k = a;
    if a & 1 == 0 {
        k = k.wrapping_add(1);
    } else {
        out.write(1);
    }
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
    k
}

// UNSOUND: `x` is uninitialized whenever `a & 1 == 0`.
#[rapx::verify]
pub fn unsound_write_past_path_limit(a: u32) -> u32 {
    let mut x = MaybeUninit::uninit();
    let k = maybe_init(&mut x, a);
    unsafe { x.assume_init() }.wrapping_add(k)
}
