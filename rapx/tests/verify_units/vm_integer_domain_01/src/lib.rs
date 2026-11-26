#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

// The contracts constrain a widened value. Its destination type alone cannot
// establish these bounds: the VM must retain the source parameter's domain.
#[rapx::requires(ValidNum(_value >= 0), kind = "precond")]
#[rapx::requires(ValidNum(_value <= 65535), kind = "precond")]
unsafe fn require_u16_domain(_value: i32) {}

#[rapx::requires(ValidNum(_value >= -128), kind = "precond")]
#[rapx::requires(ValidNum(_value <= 127), kind = "precond")]
unsafe fn require_i8_domain(_value: i16) {}

#[rapx::requires(ValidNum(_value < 255), kind = "precond")]
unsafe fn require_below_u8_max(_value: u16) {}

#[rapx::requires(ValidNum(_value >= 0), kind = "precond")]
unsafe fn require_nonnegative(_value: i16) {}

pub struct SignedField {
    pub value: i8,
}

#[rapx::verify]
pub fn sound_unsigned_parameter(value: u16) {
    unsafe { require_u16_domain(value as i32) };
}

#[rapx::verify]
pub fn sound_signed_parameter(value: i8) {
    unsafe { require_i8_domain(value as i16) };
}

#[rapx::verify]
pub fn sound_struct_field(value: SignedField) {
    unsafe { require_i8_domain(value.value as i16) };
}

#[rapx::verify]
pub fn sound_reference_parameter(value: &u16) {
    unsafe { require_u16_domain(*value as i32) };
}

#[rapx::verify]
pub fn sound_overwritten_parameter(mut value: u16, replace: bool) {
    let original = value as i32;
    if replace {
        value = 0;
    }
    unsafe {
        require_u16_domain(original);
        require_u16_domain(value as i32);
    }
}

// A valid input at the maximum/minimum must remain feasible. Overconstraining
// the incoming domain would incorrectly discharge these stronger contracts.
#[rapx::verify]
pub fn unsound_unsigned_maximum(value: u8) {
    unsafe { require_below_u8_max(value as u16) };
}

#[rapx::verify]
pub fn unsound_signed_negative(value: i8) {
    unsafe { require_nonnegative(value as i16) };
}
