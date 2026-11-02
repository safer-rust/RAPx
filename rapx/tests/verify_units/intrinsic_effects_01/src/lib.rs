#![feature(register_tool, core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code, internal_features, unused_variables)]

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::verify]
pub fn unsound_after_write_bytes() {
    let mut value = 1_u32;
    unsafe { std::intrinsics::write_bytes(&mut value, 0, 1) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_after_write_bytes() {
    let mut value = 0_u32;
    unsafe { std::intrinsics::write_bytes(&mut value, 1, 1) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_after_zero_count_write_bytes() {
    let mut value = 1_u32;
    unsafe { std::intrinsics::write_bytes(&mut value, 0, 0) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn unknown_after_symbolic_write_bytes(byte: u8) {
    let mut value = 1_u32;
    unsafe { std::intrinsics::write_bytes(&mut value, byte, 1) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn sound_after_array_fill() {
    let mut bytes = [0_u8; 8];
    unsafe { std::intrinsics::write_bytes(&mut bytes, 0xff, 1) };
    unsafe { need_nonzero(bytes[0] as u32) };
}

#[rapx::verify]
pub fn unsound_after_array_fill() {
    let mut bytes = [1_u8; 8];
    unsafe { std::intrinsics::write_bytes(&mut bytes, 0, 1) };
    unsafe { need_nonzero(bytes[0] as u32) };
}

#[rapx::verify]
pub fn sound_raw_eq_same_pointer() {
    let value = 1_u64;
    let equal = unsafe { std::intrinsics::raw_eq(&value, &value) };
    if !equal {
        unsafe { need_nonzero(0) };
    }
}

#[rapx::verify]
pub fn sound_raw_eq_equal_values() {
    let first = 1_u64;
    let second = 1_u64;
    let equal = unsafe { std::intrinsics::raw_eq(&first, &second) };
    if !equal {
        unsafe { need_nonzero(0) };
    }
}

#[rapx::verify]
pub fn sound_after_exact_div() {
    let quotient = unsafe { std::intrinsics::exact_div(4_u32, 2_u32) };
    if quotient != 2 {
        unsafe { need_nonzero(0) };
    }
}

#[rapx::verify]
pub fn unknown_after_float_to_int() {
    let converted: u32 = unsafe { std::intrinsics::float_to_int_unchecked(1.0_f32) };
    if converted != 1 {
        unsafe { need_nonzero(0) };
    }
}

#[rapx::verify]
pub fn unsound_after_typed_swap() {
    let mut first = 1_u32;
    let mut second = 0_u32;
    unsafe { std::intrinsics::typed_swap_nonoverlapping(&mut first, &mut second) };
    unsafe { need_nonzero(first) };
}

#[rapx::verify]
pub fn sound_after_typed_swap() {
    let mut first = 0_u32;
    let mut second = 1_u32;
    unsafe { std::intrinsics::typed_swap_nonoverlapping(&mut first, &mut second) };
    unsafe { need_nonzero(first) };
}
