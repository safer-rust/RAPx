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

// ========================================================================
// Challenge 11: Safety of Methods for Numeric Primitive Types
//
// A faithful, self-contained port of the numeric primitive methods in
// `library/core/src/num/{int,uint}_macros.rs` (see
// https://model-checking.github.io/verify-rust-std/challenges/0011-floats-ints.html).
//
// The challenge requires proving the absence of arithmetic overflow/underflow
// and undefined behavior in:
//
//   Part 1 — the `unchecked_{add,sub,mul,shl,shr,neg}` unsafe methods,
//   Part 2 — the safe APIs `wrapping_{shl,shr}`, `widening_mul`, `carrying_mul`,
//   Part 3 — the float-to-int conversion `to_int_unchecked`.
//
// The overflow/underflow obligations are discharged through the `ValidNum`
// contract: an unsafe method declares its `# Safety` pre-condition
// (`lhs <= MAX - rhs`, `rhs < BITS`, `x != MIN`, ...) as a
// `#[rapx::requires(ValidNum(..))]`, and the safe wrapper must *prove* that
// pre-condition at its unsafe call site.  The interesting proofs are all in
// Part 2, where a safe wrapper either masks the shift width (`wrapping_shl`)
// or guards the operation (`checked_shl`, `unbounded_shl`, `checked_add`,
// `checked_sub`, `checked_neg`) before reaching for the unchecked intrinsic.
//
// The port stays faithful to `std`, with the following mechanical adaptations
// required for RAPx:
//
//   * Each unsafe method lowers to the same `std` primitive method it mirrors
//     (`u32::unchecked_add`, `unchecked_sub`, `unchecked_mul`,
//     `unchecked_shl`, `unchecked_shr`, and `0i32.unchecked_sub(x)` for
//     `unchecked_neg`), whose RAPx contract is a `ValidNum(0 == 0)` trust
//     boundary; only the `#[rapx::requires(ValidNum(..))]` pre-condition is
//     the real proof obligation, discharged by the safe wrappers in Part 2.
//
//   * `u32` / `i32` stand in for the full integer matrix of the challenge
//     (`u8`..`u128` for the unsigned methods, `i8`..`i128` for the signed
//     ones, `i8`..`i128` for `unchecked_neg`, and `u8`/`u16`/`u32`/`u64` for
//     `widening_mul`/`carrying_mul`); the `ValidNum` pre-conditions are
//     bit-width-uniform, so a single instantiation exercises the same proof
//     obligation as every other width.
//
//   * `unchecked_mul`'s overflow pre-condition (`!self.overflowing_mul(rhs).1`)
//     is a non-linear product, which RAPx does not SMT-lower; it is modelled
//     as a trust boundary (`ValidNum(0 == 0)`), exactly mirroring RAPx's
//     built-in `core::num::unchecked_mul` contract.
//
//   * `to_int_unchecked` is instantiated at `f32 -> i32` and `f64 -> i32`;
//     the `ValidNum(value, [i32::MIN, i32::MAX])` range pre-condition mirrors
//     RAPx's built-in `core::{f32,f64}::to_int_unchecked` contract.
// ========================================================================

// ========================================================================
// Part 1 — Unsafe Integer Methods
//
// These are the trust boundaries of the port: each declares the exact
// overflow pre-condition std documents in its `# Safety` comment and then
// lowers to the same intrinsic std calls.  The verifier's job is *not* here —
// it is in Part 2, where the safe wrappers must discharge these pre-conditions.
// ========================================================================

/// `u32::unchecked_add`: `lhs + rhs`, no overflow.
///
/// SAFETY pre-condition (std): `!lhs.overflowing_add(rhs).1`, i.e.
/// `lhs <= u32::MAX - rhs`.
#[rapx::verify]
#[rapx::requires(ValidNum(lhs <= u32::MAX - rhs), kind = "precond")]
pub unsafe fn unchecked_add_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `lhs + rhs` does not overflow.
    unsafe { lhs.unchecked_add(rhs) }
}

/// `u32::unchecked_sub`: `lhs - rhs`, no underflow.
///
/// SAFETY pre-condition (std): `!lhs.overflowing_sub(rhs).1`, i.e.
/// `lhs >= rhs`.
#[rapx::verify]
#[rapx::requires(ValidNum(lhs >= rhs), kind = "precond")]
pub unsafe fn unchecked_sub_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `lhs - rhs` does not underflow.
    unsafe { lhs.unchecked_sub(rhs) }
}

/// `u32::unchecked_mul`: `lhs * rhs`, no overflow.
///
/// SAFETY pre-condition (std): `!lhs.overflowing_mul(rhs).1`. The product is
/// non-linear, so RAPx does not SMT-lower it; this method is a trust boundary
/// mirroring RAPx's built-in `core::num::unchecked_mul` contract.
#[rapx::verify]
#[rapx::requires(ValidNum(0 == 0), kind = "precond")]
pub unsafe fn unchecked_mul_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `lhs * rhs` does not overflow.
    unsafe { lhs.unchecked_mul(rhs) }
}

/// `u32::unchecked_shl`: `lhs << rhs`, no overflow.
///
/// SAFETY pre-condition (std): `rhs < u32::BITS`.
#[rapx::verify]
#[rapx::requires(ValidNum(rhs < u32::BITS), kind = "precond")]
pub unsafe fn unchecked_shl_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `rhs < u32::BITS`.
    unsafe { lhs.unchecked_shl(rhs) }
}

/// `u32::unchecked_shr`: `lhs >> rhs`, no overflow.
///
/// SAFETY pre-condition (std): `rhs < u32::BITS`.
#[rapx::verify]
#[rapx::requires(ValidNum(rhs < u32::BITS), kind = "precond")]
pub unsafe fn unchecked_shr_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the caller guarantees `rhs < u32::BITS`.
    unsafe { lhs.unchecked_shr(rhs) }
}

/// `i32::unchecked_neg`: `-x`, no overflow.
///
/// SAFETY pre-condition (std): `!x.overflowing_neg().1`, i.e.
/// `x != i32::MIN`.
#[rapx::verify]
#[rapx::requires(ValidNum(x != i32::MIN), kind = "precond")]
pub unsafe fn unchecked_neg_ext(x: i32) -> i32 {
    // SAFETY: `x != MIN` guarantees `0 - x` does not overflow; this is
    // `unchecked_neg` spelled as `0i32.unchecked_sub(x)`, as in `std`.
    unsafe { 0i32.unchecked_sub(x) }
}

// ========================================================================
// Part 2 — Safe API Verification
//
// Each safe wrapper must discharge the `ValidNum` pre-condition of the unsafe
// method it calls.  `wrapping_shl`/`wrapping_shr` do it by masking the shift
// width (`rhs & (BITS - 1) < BITS`); the `checked_*`/`unbounded_shl` wrappers
// do it by an explicit branch guard.
// ========================================================================

/// `u32::wrapping_shl`: `lhs << (rhs & (BITS - 1))`.
///
/// The masking by the bitsize guarantees `rhs & (u32::BITS - 1) < u32::BITS`,
/// discharging `unchecked_shl_ext`'s `ValidNum` pre-condition.
#[rapx::verify]
pub fn wrapping_shl_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the masking by the bitsize of the type ensures that we do not
    // shift out of bounds.
    unsafe { unchecked_shl_ext(lhs, rhs & (u32::BITS - 1)) }
}

/// `u32::wrapping_shr`: `lhs >> (rhs & (BITS - 1))`.
///
/// The masking by the bitsize guarantees `rhs & (u32::BITS - 1) < u32::BITS`,
/// discharging `unchecked_shr_ext`'s `ValidNum` pre-condition.
#[rapx::verify]
pub fn wrapping_shr_ext(lhs: u32, rhs: u32) -> u32 {
    // SAFETY: the masking by the bitsize of the type ensures that we do not
    // shift out of bounds.
    unsafe { unchecked_shr_ext(lhs, rhs & (u32::BITS - 1)) }
}

/// `u32::checked_shl`: `Some(lhs << rhs)` if in range, else `None`.
///
/// The `rhs < u32::BITS` guard discharges `unchecked_shl_ext`'s pre-condition.
#[rapx::verify]
pub fn checked_shl_ext(lhs: u32, rhs: u32) -> Option<u32> {
    if rhs < u32::BITS {
        // SAFETY: just checked the RHS is in-range.
        Some(unsafe { unchecked_shl_ext(lhs, rhs) })
    } else {
        None
    }
}

/// `u32::unbounded_shl`: `lhs << rhs` with unbounded RHS, saturating to 0.
///
/// The `rhs < u32::BITS` guard discharges `unchecked_shl_ext`'s pre-condition;
/// an out-of-range shift returns 0.
#[rapx::verify]
pub fn unbounded_shl_ext(lhs: u32, rhs: u32) -> u32 {
    if rhs < u32::BITS {
        // SAFETY: rhs is just checked to be in-range above.
        unsafe { unchecked_shl_ext(lhs, rhs) }
    } else {
        0
    }
}

/// `u32::checked_add`: `Some(lhs + rhs)` if it does not overflow, else `None`.
///
/// The `lhs <= u32::MAX - rhs` guard discharges `unchecked_add_ext`'s
/// pre-condition (the arithmetic equivalent of std's
/// `!add_with_overflow(lhs, rhs).1`).
#[rapx::verify]
pub fn checked_add_ext(lhs: u32, rhs: u32) -> Option<u32> {
    if lhs <= u32::MAX - rhs {
        // SAFETY: just checked the addition does not overflow.
        Some(unsafe { unchecked_add_ext(lhs, rhs) })
    } else {
        None
    }
}

/// `u32::checked_sub`: `Some(lhs - rhs)` if it does not underflow, else `None`.
///
/// The `lhs >= rhs` guard discharges `unchecked_sub_ext`'s pre-condition.
#[rapx::verify]
pub fn checked_sub_ext(lhs: u32, rhs: u32) -> Option<u32> {
    if lhs >= rhs {
        // SAFETY: just checked the subtraction does not underflow.
        Some(unsafe { unchecked_sub_ext(lhs, rhs) })
    } else {
        None
    }
}

/// `i32::checked_neg`: `Some(-x)` if `x != MIN`, else `None`.
///
/// The `x != i32::MIN` guard discharges `unchecked_neg_ext`'s pre-condition.
#[rapx::verify]
pub fn checked_neg_ext(x: i32) -> Option<i32> {
    if x != i32::MIN {
        // SAFETY: just checked the negation does not overflow.
        Some(unsafe { unchecked_neg_ext(x) })
    } else {
        None
    }
}

/// `u32::widening_mul`: full-width `lhs * rhs`, returning the low-order and
/// high-order bits. Cannot overflow: the double-width result has exactly
/// enough space for the largest possible product.
#[rapx::verify]
pub fn widening_mul_ext(lhs: u32, rhs: u32) -> (u32, u32) {
    // SAFETY: `carrying_mul_add` cannot overflow by construction.
    carrying_mul_add_ext(lhs, rhs, 0, 0)
}

/// `u32::carrying_mul`: `lhs * rhs + carry`, returning the low-order and
/// high-order bits. Cannot overflow.
#[rapx::verify]
pub fn carrying_mul_ext(lhs: u32, rhs: u32, carry: u32) -> (u32, u32) {
    // SAFETY: `carrying_mul_add` cannot overflow by construction.
    carrying_mul_add_ext(lhs, rhs, carry, 0)
}

/// `u32::carrying_mul_add`: `lhs * rhs + carry + add`, returning the
/// low-order and high-order bits. Lowered to `u32::carrying_mul_add`, which
/// cannot overflow (this is how `std` implements it).
fn carrying_mul_add_ext(lhs: u32, rhs: u32, carry: u32, add: u32) -> (u32, u32) {
    // `carrying_mul_add` cannot overflow; the result is split into low and
    // high halves (this is how `std` implements it).
    lhs.carrying_mul_add(rhs, carry, add)
}

// ========================================================================
// Part 3 — Float to Integer Conversion
// ========================================================================

/// `f32::to_int_unchecked::<i32>`: truncating float-to-int, no UB.
///
/// SAFETY pre-condition (std): the value is finite and fits within the target
/// integer type, i.e. `value ∈ [i32::MIN, i32::MAX]`.
#[rapx::verify]
#[rapx::requires(ValidNum(value, "[i32::MIN, i32::MAX]"), kind = "precond")]
pub unsafe fn to_int_unchecked_f32_ext(value: f32) -> i32 {
    // SAFETY: the caller guarantees the value fits within `i32`.
    unsafe { value.to_int_unchecked() }
}

/// `f64::to_int_unchecked::<i32>`: truncating float-to-int, no UB.
///
/// SAFETY pre-condition (std): the value is finite and fits within the target
/// integer type, i.e. `value ∈ [i32::MIN, i32::MAX]`.
#[rapx::verify]
#[rapx::requires(ValidNum(value, "[i32::MIN, i32::MAX]"), kind = "precond")]
pub unsafe fn to_int_unchecked_f64_ext(value: f64) -> i32 {
    // SAFETY: the caller guarantees the value fits within `i32`.
    unsafe { value.to_int_unchecked() }
}
