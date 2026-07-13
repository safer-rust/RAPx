#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::num::NonZero;

struct MyType(u16, u8);

// UNSOUND: `MyType(u16, u8)` → `NonZero<u16>` without `TransmuteWithoutAlign` contract.
// `NonZero<u16>` has non-trivial type_invariant (value ≠ 0).
#[rapx::verify]
pub fn align_to_nonzero_u16(slice: &[MyType]) -> (&[MyType], &[NonZero<u16>], &[MyType]) {
    unsafe { slice.align_to::<NonZero<u16>>() }
}

// UNSOUND: `MyType(u16, u8)` → `NonZero<u32>` without contract.
#[rapx::verify]
pub fn align_to_nonzero_u32(slice: &[MyType]) -> (&[MyType], &[NonZero<u32>], &[MyType]) {
    unsafe { slice.align_to::<NonZero<u32>>() }
}

// UNSOUND: `MyType(u16, u8)` → `NonZero<u8>` without contract.
#[rapx::verify]
pub fn align_to_nonzero_u8(slice: &[MyType]) -> (&[MyType], &[NonZero<u8>], &[MyType]) {
    unsafe { slice.align_to::<NonZero<u8>>() }
}
