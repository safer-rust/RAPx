#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

struct MyType(u16, u8);

// UNSOUND: generic `T, U` without `TransmuteWithoutAlign` contract.
#[rapx::verify]
pub fn align_without_contract_generic<T, U>(slice: &[T]) -> (&[T], &[U], &[T]) {
    unsafe { slice.align_to::<U>() }
}

// UNSOUND: `align_to::<u32>` without `TransmuteWithoutAlign` contract.
#[rapx::verify]
pub fn align_without_contract_u32(slice: &[MyType]) -> (&[MyType], &[u32], &[MyType]) {
    unsafe { slice.align_to::<u32>() }
}

// UNSOUND: `align_to::<u16>` without `TransmuteWithoutAlign` contract.
#[rapx::verify]
pub fn align_without_contract_u16(slice: &[MyType]) -> (&[MyType], &[u16], &[MyType]) {
    unsafe { slice.align_to::<u16>() }
}

// UNSOUND: `align_to::<u8>` without `TransmuteWithoutAlign` contract.
#[rapx::verify]
pub fn align_without_contract_u8(slice: &[MyType]) -> (&[MyType], &[u8], &[MyType]) {
    unsafe { slice.align_to::<u8>() }
}
