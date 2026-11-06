#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_variables)]

#[rapx::requires(ValidNum(value != 0), kind = "precond")]
unsafe fn require_nonzero(value: u8) {}

#[rapx::requires(ValidNum(value == 0), kind = "precond")]
unsafe fn require_zero_u8(value: u8) {}

#[rapx::requires(ValidNum(value == 0), kind = "precond")]
unsafe fn require_zero_u128(value: u128) {}

#[rapx::requires(ValidNum(value == 18446744073709551616), kind = "precond")]
unsafe fn require_big(value: u128) {}

#[rapx::requires(ValidNum(value == 36893488147419103232), kind = "precond")]
unsafe fn require_twice_big(value: u128) {}

#[rapx::requires(ValidNum(value == 340282366920938463463374607431768211455), kind = "precond")]
unsafe fn require_max(value: u128) {}

struct Pair {
    number: u128,
}

const PAIR: Pair = Pair {
    number: 1u128 << 64,
};

const MAX_PAIR: Pair = Pair { number: u128::MAX };

#[rapx::verify]
pub fn boxed_zero_sound() {
    let value = Box::new((5u8, 0u8));
    unsafe { require_zero_u8(value.1) };
}

#[rapx::verify]
pub fn boxed_zero_unsound() {
    let value = Box::new((5u8, 0u8));
    unsafe { require_nonzero(value.1) };
}

#[rapx::verify]
pub fn boxed_unknown_unsound(value: Box<(u8, u8)>) {
    unsafe { require_nonzero(value.1) };
}

#[rapx::verify]
pub fn boxed_scalar_sound() {
    let value = Box::new(0u8);
    unsafe { require_zero_u8(*value) };
}

#[rapx::verify]
pub fn boxed_scalar_unsound() {
    let value = Box::new(0u8);
    unsafe { require_nonzero(*value) };
}

#[rapx::verify]
pub fn constant_big_sound() {
    let pair = PAIR;
    unsafe { require_big(pair.number) };
}

#[rapx::verify]
pub fn constant_zero_unsound() {
    let pair = PAIR;
    unsafe { require_zero_u128(pair.number) };
}

#[rapx::verify]
pub fn maximum_constant_sound() {
    let pair = MAX_PAIR;
    unsafe { require_max(pair.number) };
}

#[rapx::verify]
pub fn shifted_big_sound() {
    unsafe { require_big(1u128 << 64) };
}

#[rapx::verify]
pub fn shifted_twice_big_sound() {
    unsafe { require_twice_big((1u128 << 64) << 1) };
}

#[rapx::verify]
pub fn literal_big_sound() {
    unsafe { require_big(18446744073709551616u128) };
}
