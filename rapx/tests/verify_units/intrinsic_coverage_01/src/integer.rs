use super::need_nonzero;
use core::intrinsics;

#[rapx::verify]
pub fn integer_intrinsics(value: u32, shift: u32) {
    let nonzero = value | 1;
    let a = intrinsics::ctpop(value);
    let b = intrinsics::cttz(value);
    let c = intrinsics::ctlz(value);
    let d = unsafe { intrinsics::cttz_nonzero(nonzero) };
    let e = unsafe { intrinsics::ctlz_nonzero(nonzero) };
    let f = intrinsics::bswap(value);
    let g = intrinsics::bitreverse(value);
    let h = intrinsics::rotate_left(value, shift);
    let i = intrinsics::rotate_right(value, shift);
    let j = intrinsics::saturating_add(value, nonzero);
    let k = intrinsics::saturating_sub(value, nonzero);
    let l = intrinsics::wrapping_add(value, nonzero);
    let m = intrinsics::wrapping_sub(value, nonzero);
    let n = intrinsics::wrapping_mul(value, nonzero);
    let o = unsafe { intrinsics::unchecked_add(nonzero, 0) };
    let p = unsafe { intrinsics::unchecked_sub(nonzero, 0) };
    let q = unsafe { intrinsics::unchecked_mul(nonzero, 1) };
    let r = intrinsics::add_with_overflow(value, nonzero).0;
    let s = intrinsics::sub_with_overflow(value, nonzero).0;
    let t = intrinsics::mul_with_overflow(value, nonzero).0;
    #[cfg(rapx_ge_100)]
    let u = intrinsics::integer_min(value, nonzero);
    #[cfg(not(rapx_ge_100))]
    let u = value.min(nonzero);
    #[cfg(rapx_ge_100)]
    let v = intrinsics::integer_max(value, nonzero);
    #[cfg(not(rapx_ge_100))]
    let v = value.max(nonzero);
    let w = intrinsics::select_unpredictable(value != 0, u, v);
    let x = intrinsics::likely(value != 0) as u32;
    let y = intrinsics::unlikely(value == 0) as u32;
    let z = intrinsics::black_box(nonzero);
    let sum = a
        ^ b
        ^ c
        ^ d
        ^ e
        ^ f
        ^ g
        ^ h
        ^ i
        ^ j
        ^ k
        ^ l
        ^ m
        ^ n
        ^ o
        ^ p
        ^ q
        ^ r
        ^ s
        ^ t
        ^ u
        ^ v
        ^ w
        ^ x
        ^ y
        ^ z;
    unsafe { need_nonzero(sum) };
}

#[rapx::verify]
pub fn integer_arithmetic_intrinsics(value: u32) {
    let nonzero = value | 1;
    let divided = unsafe { intrinsics::unchecked_div(nonzero, 1) };
    let remainder = unsafe { intrinsics::unchecked_rem(nonzero, 1) };
    let exact = unsafe { intrinsics::exact_div(nonzero, 1) };
    let shifted_left = unsafe { intrinsics::unchecked_shl(nonzero, 0_u32) };
    let shifted_right = unsafe { intrinsics::unchecked_shr(nonzero, 0_u32) };
    let funnel_left = unsafe { intrinsics::unchecked_funnel_shl(nonzero, nonzero, 0) };
    let funnel_right = unsafe { intrinsics::unchecked_funnel_shr(nonzero, nonzero, 0) };
    let carryless = intrinsics::carryless_mul(nonzero, 1);
    let disjoint = unsafe { intrinsics::disjoint_bitor(value & 1, value & !1) };
    let (low, carry) = intrinsics::carrying_mul_add(nonzero, 1, 0, 0);
    let compared = intrinsics::three_way_compare(nonzero, value) as i32;
    unsafe {
        need_nonzero(
            divided
                ^ remainder
                ^ exact
                ^ shifted_left
                ^ shifted_right
                ^ funnel_left
                ^ funnel_right
                ^ carryless
                ^ disjoint
                ^ low
                ^ carry
                ^ (compared as u32),
        )
    };
}

#[rapx::verify]
pub fn integer_control_intrinsics(value: u32) {
    unsafe { intrinsics::assume(true) };
    let known = intrinsics::is_val_statically_known(value) as u32;
    let overflow = intrinsics::overflow_checks() as u32;
    let ub = intrinsics::ub_checks() as u32;
    unsafe { need_nonzero(known ^ overflow ^ ub ^ value) };
}
