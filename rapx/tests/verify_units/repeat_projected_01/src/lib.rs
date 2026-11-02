#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::requires(ValidNum(value == 1))]
unsafe fn expect_one(value: u8) {}

#[rapx::verify]
pub fn symbolic_index_repeat_sound(index: usize) {
    let mut arrays = [[0u8; 2]; 2];
    if index < 2 {
        arrays[index] = [1u8; 2];
        unsafe { expect_one(arrays[index][0]) };
    }
}

#[rapx::verify]
pub fn symbolic_index_repeat_unsound(index: usize) {
    let mut arrays = [[1u8; 2]; 2];
    if index < 2 {
        arrays[index] = [0u8; 2];
        unsafe { expect_one(arrays[index][0]) };
    }
}

#[rapx::verify]
pub fn symbolic_index_repeat_overwrite_unsound(index: usize) {
    let mut arrays = [[0u8; 2]; 2];
    if index < 2 {
        arrays[index] = [1u8; 2];
        arrays[index][0] = 0;
        unsafe { expect_one(arrays[index][0]) };
    }
}
