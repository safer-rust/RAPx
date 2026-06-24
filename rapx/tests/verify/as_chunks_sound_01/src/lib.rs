#![feature(register_tool)]
#![feature(core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `N` is a nonzero const generic and the path guard proves exact division.
#[rapx::verify]
pub fn sound_as_chunks_unchecked_exact_div(data: &[u32]) -> usize {
    if data.len() % 4 == 0 {
        let chunks = unsafe { data.as_chunks_unchecked::<4>() };
        chunks.len()
    } else {
        0
    }
}

// SOUND: `exact_div` is guarded by the same divisor and divisibility condition.
#[rapx::verify]
pub fn sound_exact_div_guard(data: &[u32]) -> usize {
    if data.len() % 4 == 0 {
        unsafe { core::intrinsics::exact_div(data.len(), 4) }
    } else {
        0
    }
}
