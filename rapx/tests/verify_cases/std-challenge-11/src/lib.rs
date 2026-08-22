#![feature(register_tool)]
#![register_tool(rapx)]
// `unchecked_shl`/`unchecked_shr` are `unchecked_shifts`-gated on the
// verify-std toolchain (nightly-2025-11-25) but stable since 1.93; the
// feature gate + `stable_features` allow keeps all three CI toolchains happy.
#![feature(unchecked_shifts)]
#![allow(stable_features)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(dead_code)]
#![allow(unused_comparisons)]

// Challenge 11: Safety of numeric primitive methods — a faithful, self-contained
// port of the numeric methods in `library/core/src/num/{int,uint}_macros.rs`.
// `u32`/`i32` stand in for the full integer matrix; the `ValidNum` pre-conditions
// are bit-width-uniform.

/// `u32::unchecked_add`: `lhs + rhs`, no overflow; requires `lhs <= u32::MAX - rhs`.
#[rapx::verify]
#[rapx::requires(ValidNum(lhs <= u32::MAX - rhs), kind = "precond")]
pub unsafe fn unchecked_add_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `lhs + rhs` does not overflow.
    unsafe { lhs.unchecked_add(rhs) }
}

/// `u32::unchecked_sub`: `lhs - rhs`, no underflow; requires `lhs >= rhs`.
#[rapx::verify]
#[rapx::requires(ValidNum(lhs >= rhs), kind = "precond")]
pub unsafe fn unchecked_sub_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `lhs - rhs` does not underflow.
    unsafe { lhs.unchecked_sub(rhs) }
}

/// `u32::unchecked_mul`: `lhs * rhs`, no overflow (non-linear product is a trust boundary).
#[rapx::verify]
#[rapx::requires(ValidNum(0 == 0), kind = "precond")]
pub unsafe fn unchecked_mul_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `lhs * rhs` does not overflow.
    unsafe { lhs.unchecked_mul(rhs) }
}

/// `u32::unchecked_shl`: `lhs << rhs`, no overflow; requires `rhs < u32::BITS`.
#[rapx::verify]
#[rapx::requires(ValidNum(rhs < u32::BITS), kind = "precond")]
pub unsafe fn unchecked_shl_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `rhs < u32::BITS`.
    unsafe { lhs.unchecked_shl(rhs) }
}

/// `u32::unchecked_shr`: `lhs >> rhs`, no overflow; requires `rhs < u32::BITS`.
#[rapx::verify]
#[rapx::requires(ValidNum(rhs < u32::BITS), kind = "precond")]
pub unsafe fn unchecked_shr_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `rhs < u32::BITS`.
    unsafe { lhs.unchecked_shr(rhs) }
}

/// `i32::unchecked_neg`: `-x`, no overflow; requires `x != i32::MIN`.
#[rapx::verify]
#[rapx::requires(ValidNum(x != i32::MIN), kind = "precond")]
pub unsafe fn unchecked_neg_ext(x: i32) -> i32 {
    // SAFETY: `x != MIN` guarantees `0 - x` does not overflow; this is
    // `unchecked_neg` spelled as `0i32.unchecked_sub(x)`, as in `std`.
    unsafe { 0i32.unchecked_sub(x) }
}

/// `u32::wrapping_shl`: `lhs << (rhs & (BITS - 1))`; the masking guarantees `rhs & (u32::BITS - 1) < u32::BITS`.
#[rapx::verify]
pub fn wrapping_shl_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the masking by the bitsize of the type ensures that we do not
    // shift out of bounds.
    unsafe { unchecked_shl_ext(lhs, rhs & (u32::BITS - 1)) }
}

/// `u32::wrapping_shr`: `lhs >> (rhs & (BITS - 1))`; the masking guarantees `rhs & (u32::BITS - 1) < u32::BITS`.
#[rapx::verify]
pub fn wrapping_shr_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the masking by the bitsize of the type ensures that we do not
    // shift out of bounds.
    unsafe { unchecked_shr_ext(lhs, rhs & (u32::BITS - 1)) }
}

/// `u32::checked_shl`: `Some(lhs << rhs)` if in range, else `None`; the `rhs < u32::BITS` guard discharges the pre-condition.
#[rapx::verify]
pub fn checked_shl_ext(lhs: u32, rhs: u32) -> Option<u32> {
    if rhs < u32::BITS {
        // SAFETY: just checked the RHS is in-range.
        Some(unsafe { unchecked_shl_ext(lhs, rhs) })
    } else {
        None
    }
}

/// `u32::unbounded_shl`: `lhs << rhs` with unbounded RHS, saturating to 0; the `rhs < u32::BITS` guard discharges the pre-condition.
#[rapx::verify]
pub fn unbounded_shl_ext(lhs: u32, rhs: u32) -> u32 {
    if rhs < u32::BITS {
        // SAFETY: rhs is just checked to be in-range above.
        unsafe { unchecked_shl_ext(lhs, rhs) }
    } else {
        0
    }
}

/// `u32::checked_add`: `Some(lhs + rhs)` if it does not overflow, else `None`; guarded by `lhs <= u32::MAX - rhs`.
#[rapx::verify]
pub fn checked_add_ext(lhs: u32, rhs: u32) -> Option<u32> {
    if lhs <= u32::MAX - rhs {
        // SAFETY: just checked the addition does not overflow.
        Some(unsafe { unchecked_add_ext(lhs, rhs) })
    } else {
        None
    }
}

/// `u32::checked_sub`: `Some(lhs - rhs)` if it does not underflow, else `None`; guarded by `lhs >= rhs`.
#[rapx::verify]
pub fn checked_sub_ext(lhs: u32, rhs: u32) -> Option<u32> {
    if lhs >= rhs {
        // SAFETY: just checked the subtraction does not underflow.
        Some(unsafe { unchecked_sub_ext(lhs, rhs) })
    } else {
        None
    }
}

/// `i32::checked_neg`: `Some(-x)` if `x != MIN`, else `None`; guarded by `x != i32::MIN`.
#[rapx::verify]
pub fn checked_neg_ext(x: i32) -> Option<i32> {
    if x != i32::MIN {
        // SAFETY: just checked the negation does not overflow.
        Some(unsafe { unchecked_neg_ext(x) })
    } else {
        None
    }
}

/// `u32::widening_mul`: full-width `lhs * rhs`, returning low-order and high-order bits (cannot overflow).
#[rapx::verify]
pub fn widening_mul_ext(lhs: u32, rhs: u32) -> (u32, u32) {
    // SAFETY: `carrying_mul_add` cannot overflow by construction.
    carrying_mul_add_ext(lhs, rhs, 0, 0)
}

/// `u32::carrying_mul`: `lhs * rhs + carry`, returning low-order and high-order bits (cannot overflow).
#[rapx::verify]
pub fn carrying_mul_ext(lhs: u32, rhs: u32, carry: u32) -> (u32, u32) {
    // SAFETY: `carrying_mul_add` cannot overflow by construction.
    carrying_mul_add_ext(lhs, rhs, carry, 0)
}

/// `u32::carrying_mul_add`: `lhs * rhs + carry + add`, lowered to `u32::carrying_mul_add` (cannot overflow).
fn carrying_mul_add_ext(lhs: u32, rhs: u32, carry: u32, add: u32) -> (u32, u32) {
    // `carrying_mul_add` cannot overflow; the result is split into low and
    // high halves (this is how `std` implements it).
    lhs.carrying_mul_add(rhs, carry, add)
}

/// `f32::to_int_unchecked::<i32>`: truncating float-to-int, no UB; requires the value be finite and in `[i32::MIN, i32::MAX]`.
#[rapx::verify]
#[rapx::requires(ValidNum(value, "[i32::MIN, i32::MAX]"), kind = "precond")]
pub unsafe fn to_int_unchecked_f32_ext(value: f32) -> i32 {
    // SAFETY: the caller guarantees the value fits within `i32`.
    unsafe { value.to_int_unchecked() }
}

/// `f64::to_int_unchecked::<i32>`: truncating float-to-int, no UB; requires the value be finite and in `[i32::MIN, i32::MAX]`.
#[rapx::verify]
#[rapx::requires(ValidNum(value, "[i32::MIN, i32::MAX]"), kind = "precond")]
pub unsafe fn to_int_unchecked_f64_ext(value: f64) -> i32 {
    // SAFETY: the caller guarantees the value fits within `i32`.
    unsafe { value.to_int_unchecked() }
}
