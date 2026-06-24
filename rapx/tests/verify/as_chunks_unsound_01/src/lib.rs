#![feature(register_tool)]
#![feature(core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: `N` is nonzero, but there is no guard proving `data.len() % N == 0`.
#[rapx::verify]
pub fn unsound_as_chunks_unchecked_missing_exact_div(data: &[u32]) -> usize {
    let chunks = unsafe { data.as_chunks_unchecked::<4>() };
    chunks.len()
}

// UNSOUND: the divisor is nonzero, but the exact-division precondition is missing.
#[rapx::verify]
pub fn unsound_exact_div_missing_guard(data: &[u32]) -> usize {
    unsafe { core::intrinsics::exact_div(data.len(), 4) }
}
