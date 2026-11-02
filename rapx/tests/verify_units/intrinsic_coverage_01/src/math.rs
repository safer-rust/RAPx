use super::need_nonzero;
use core::intrinsics;

#[cfg(rapx_generic_float_intrinsics)]
#[rapx::verify]
pub fn scalar_float_intrinsics(value: f32) {
    let input = intrinsics::fabs(value) + 1.0;
    let values = [
        intrinsics::sqrt(input),
        intrinsics::sin(input),
        intrinsics::cos(input),
        intrinsics::powf(input, 2.0),
        intrinsics::powi(input, 2),
        intrinsics::exp(input),
        intrinsics::exp2(input),
        intrinsics::log(input),
        intrinsics::log10(input),
        intrinsics::log2(input),
        intrinsics::fma(input, 2.0, 1.0),
        intrinsics::floor(input),
        intrinsics::ceil(input),
        intrinsics::trunc(input),
        intrinsics::round_ties_even(input),
        intrinsics::round(input),
        intrinsics::minimumf32(input, 2.0),
        intrinsics::maximumf32(input, 2.0),
        intrinsics::copysignf32(input, -1.0),
    ];
    let mut bits = 0_u32;
    for value in values {
        bits ^= value.to_bits();
    }
    unsafe { need_nonzero(bits) };
}

#[cfg(not(rapx_generic_float_intrinsics))]
#[rapx::verify]
pub fn scalar_float_intrinsics(value: f32) {
    let input = intrinsics::fabs(value) + 1.0;
    let values = [
        intrinsics::sqrtf32(input),
        intrinsics::powif32(input, 2),
        intrinsics::minimumf32(input, 2.0),
        intrinsics::maximumf32(input, 2.0),
        intrinsics::copysignf32(input, -1.0),
    ];
    let mut bits = 0_u32;
    for value in values {
        bits ^= value.to_bits();
    }
    unsafe { need_nonzero(bits) };
}

#[rapx::verify]
pub fn scalar_float_unchecked_intrinsics() {
    let value = 1.5_f32;
    let converted: i32 = unsafe { intrinsics::float_to_int_unchecked(value) };
    #[cfg(rapx_generic_float_intrinsics)]
    let unfused = intrinsics::fmuladd(value, 2.0, 1.0);
    #[cfg(not(rapx_generic_float_intrinsics))]
    let unfused = intrinsics::fmuladdf32(value, 2.0, 1.0);
    unsafe { need_nonzero((converted as u32) ^ unfused.to_bits()) };
}

#[rapx::verify]
pub fn scalar_float_arithmetic_intrinsics() {
    let a = 1.5_f32;
    let b = 2.0_f32;
    let values = [
        intrinsics::fadd_algebraic(a, b),
        intrinsics::fsub_algebraic(a, b),
        intrinsics::fmul_algebraic(a, b),
        intrinsics::fdiv_algebraic(a, b),
        intrinsics::frem_algebraic(a, b),
        unsafe { intrinsics::fadd_fast(a, b) },
        unsafe { intrinsics::fsub_fast(a, b) },
        unsafe { intrinsics::fmul_fast(a, b) },
        unsafe { intrinsics::fdiv_fast(a, b) },
        unsafe { intrinsics::frem_fast(a, b) },
        intrinsics::minimum_number_nsz_f32(a, b),
        intrinsics::maximum_number_nsz_f32(a, b),
    ];
    let mut bits = 0_u32;
    for value in values {
        bits ^= value.to_bits();
    }
    unsafe { need_nonzero(bits) };
}
