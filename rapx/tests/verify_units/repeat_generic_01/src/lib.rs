#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::requires(ValidNum(value == 7))]
unsafe fn expect_seven(value: u8) {}

#[rapx::verify]
pub fn generic_repeat_sound<const N: usize>() {
    let values = [7u8; N];
    if N > 0 {
        unsafe { expect_seven(values[0]) }
    }
}

#[rapx::verify]
pub fn generic_repeat_unsound<const N: usize>() {
    let values = [8u8; N];
    if N > 0 {
        unsafe { expect_seven(values[0]) }
    }
}
