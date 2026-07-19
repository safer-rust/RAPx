#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

pub struct MyType(u8, u8, u8);

/// SOUND: `SplitTransmute([MyType], [u8])` covers the transmutation;
/// `MyType` has no padding (3×u8, align 1), `u8` is all-bit-valid.
#[rapx::verify]
#[rapx::requires(SplitTransmute([MyType], [u8]))]
pub unsafe fn align_to_u8_sound(slice: &[MyType]) -> (&[MyType], &[u8], &[MyType]) {
    slice.align_to::<u8>()
}
