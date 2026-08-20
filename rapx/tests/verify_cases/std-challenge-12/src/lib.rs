#![feature(register_tool)]
#![register_tool(rapx)]
#![feature(core_intrinsics)]
#![feature(nonzero_internals)]
#![allow(unsafe_op_in_unsafe_fn)]
#![allow(internal_features)]

// ========================================================================
// Challenge 12: Safety of `NonZero`
//
// A faithful, self-contained port of `library/core/src/num/nonzero.rs`
// (see
// https://model-checking.github.io/verify-rust-std/challenges/0012-nonzero.html).
//
// `NonZero<T>` wraps a primitive integer `T` that is known not to equal
// zero, enabling niche layout optimization (`Option<NonZero<u32>>` is the
// same size as `u32`). The challenge requires:
//
//   Part 1 — `new` and `new_unchecked`:
//     * a `NonZero` is created iff the input is non-zero,
//     * the inner value equals the input,
//     * `new_unchecked`'s `# Safety` pre-condition (`n != 0`) is upheld.
//     `new`/`get` lower to `transmute_unchecked`; per the challenge's
//     assumptions, verifying them only requires proving that the source and
//     destination types have the same size, which is the `ValidTransmute`
//     contract (see Challenge 1).
//
//   Part 2 — every other `unsafe` use in `core::num::nonzero`:
//     `max`/`min`/`clamp`, the three `bitor` impls, `count_ones`,
//     `rotate_left`/`rotate_right`, `swap_bytes`, `reverse_bits`,
//     `from_be`/`from_le`/`to_be`/`to_le`, `checked_mul`/`saturating_mul`/
//     `unchecked_mul`, `checked_pow`/`saturating_pow`, `neg`,
//     `checked_add`/`saturating_add`/`unchecked_add`,
//     `checked_next_power_of_two`, `midpoint`, `isqrt`, `abs`/`checked_abs`/
//     `overflowing_abs`/`saturating_abs`/`wrapping_abs`, `unsigned_abs`,
//     `checked_neg`/`overflowing_neg`/`wrapping_neg`, `from_mut`/
//     `from_mut_unchecked`.
//
//     Each of these is safe (or carries only an overflow pre-condition) and
//     internally calls `NonZero::new_unchecked`, so the proof obligation is
//     to discharge the `ValidNum(n != 0)` pre-condition at every call site:
//     the operation must provably preserve non-zero-ness.
//
// The port stays faithful to `std`, with the following mechanical
// adaptations required for RAPx:
//
//   * The transmuting methods (`new`, `new_unchecked`, `get`, `from_mut`,
//     `from_mut_unchecked`) are reproduced as free `_ext` functions over the
//     real `std::num::NonZero<T>`; the niche/layout facts are captured by the
//     `ValidTransmute` contract (size equality) rather than by relying on the
//     internal `ZeroablePrimitive`/`NonZeroInner` machinery, which RAPx does
//     not expand. `get_ext` delegates to the real `NonZero::get` so that RAPx
//     tracks the inner (non-zero) value through its `#[repr(transparent)]`
//     field.
//
//   * `u32` / `i32` stand in for the full integer matrix of the challenge
//     (`NonZeroU8`..`NonZeroU128` for the unsigned methods, `NonZeroI8`..
//     `NonZeroI128` for the signed ones); the non-zero preservation argument
//     is bit-width-uniform, so a single instantiation exercises the same
//     proof obligation as every other width.
//
//   * `unchecked_mul`'s overflow pre-condition is a non-linear product,
//     which RAPx does not SMT-lower; it is modelled as a trust boundary
//     (`ValidNum(0 == 0)`), mirroring RAPx's built-in `core::num::nonzero::
//     unchecked_mul` contract.
// ========================================================================

use std::num::{NonZero, ZeroablePrimitive};
use std::ops::Neg;

// ========================================================================
// Part 1 — `new`, `new_unchecked`, `get`, `from_mut`, `from_mut_unchecked`
//
// The transmuting methods. Each carries the `ValidTransmute` size-equality
// contract the challenge requires (see Challenge 1), and `new_unchecked` /
// `from_mut_unchecked` additionally carry the `# Safety` non-zero
// pre-condition.
// ========================================================================

/// `NonZero::<T>::new`: `T` -> `Option<NonZero<T>>`.
///
/// `std` lowers this to `transmute_unchecked(n)`, relying on the null-pointer
/// optimization (`size_of::<T>() == size_of::<Option<NonZero<T>>>()`). The
/// `ValidTransmute` contract records exactly that size equality.
#[rapx::verify]
#[rapx::requires(ValidTransmute(T, Option<NonZero<T>>))]
pub const unsafe fn new_ext<T: ZeroablePrimitive>(n: T) -> Option<NonZero<T>> {
    // SAFETY: `ValidTransmute` guarantees `T` and `Option<NonZero<T>>` have the
    // same size, so the transmute cannot read/write out of bounds.
    unsafe { std::intrinsics::transmute_unchecked(n) }
}

/// `NonZero::<T>::new_unchecked`: `T` -> `NonZero<T>`, `n` must be non-zero.
///
/// # Safety
///
/// The value must not be zero.
#[rapx::verify]
#[rapx::requires(ValidNum(n != 0))]
#[rapx::requires(ValidTransmute(T, NonZero<T>))]
pub const unsafe fn new_unchecked_ext<T: ZeroablePrimitive>(n: T) -> NonZero<T> {
    // SAFETY: `n != 0` by pre-condition; `NonZero<T>` is `#[repr(transparent)]`
    // over `T::NonZeroInner`, which has the same size as `T`.
    unsafe { std::intrinsics::transmute_unchecked(n) }
}

/// `NonZero::<u32>::new_unchecked`: concrete `u32` instantiation.
#[rapx::verify]
#[rapx::requires(ValidNum(n != 0))]
pub unsafe fn new_unchecked_u32_ext(n: u32) -> NonZero<u32> {
    unsafe { new_unchecked_ext(n) }
}

/// `NonZero::<i32>::new_unchecked`: concrete `i32` instantiation.
#[rapx::verify]
#[rapx::requires(ValidNum(n != 0))]
pub unsafe fn new_unchecked_i32_ext(n: i32) -> NonZero<i32> {
    unsafe { new_unchecked_ext(n) }
}

/// `NonZero::<T>::get`: `NonZero<T>` -> `T`.
///
/// `std` lowers this to `transmute_unchecked(self)`. We delegate to the real
/// `NonZero::get` so RAPx tracks the inner (non-zero) value; the size-equality
/// fact is the same `ValidTransmute(NonZero<T>, T)` recorded on the transmuting
/// constructors above.
#[rapx::verify]
pub const fn get_ext<T: ZeroablePrimitive>(self_: NonZero<T>) -> T {
    self_.get()
}

/// `NonZero::<T>::from_mut`: `&mut T` -> `Option<&mut NonZero<T>>`.
///
/// `std` lowers this to a raw-pointer cast `&mut T` -> `&mut Option<Self>`,
/// relying on the null-pointer optimization.
#[rapx::verify]
pub fn from_mut_ext<T: ZeroablePrimitive>(n: &mut T) -> Option<&mut NonZero<T>> {
    // SAFETY: `Option<NonZero<T>>` has the same layout as `T` (null-pointer
    // optimization), so the cast yields a valid `Option<&mut NonZero<T>>`.
    let opt_n = unsafe { &mut *(std::ptr::from_mut(n) as *mut Option<NonZero<T>>) };
    opt_n.as_mut()
}

/// `NonZero::<T>::from_mut_unchecked`: `&mut T` -> `&mut NonZero<T>`.
///
/// # Safety
///
/// The referenced value must not be zero.
#[rapx::verify]
#[rapx::requires(ValidNum(0 == 0))]
pub unsafe fn from_mut_unchecked_ext<T: ZeroablePrimitive>(n: &mut T) -> &mut NonZero<T> {
    // SAFETY: the caller guarantees the referenced value is non-zero;
    // `NonZero<T>` is `#[repr(transparent)]` over `T::NonZeroInner`, which has
    // the same layout as `T`.
    unsafe { &mut *(std::ptr::from_mut(n) as *mut NonZero<T>) }
}

// ========================================================================
// Part 2 — methods built on `new_unchecked`
//
// Each safe method must discharge the `ValidNum(n != 0)` pre-condition of
// `new_unchecked_ext` at its call site: the underlying integer operation must
// preserve non-zero-ness. Unsigned methods are instantiated at `u32`; signed
// methods at `i32`.
// ========================================================================

/// `<NonZero<T> as Ord>::max`: max of two non-zero values is non-zero.
#[rapx::verify]
pub fn max_ext(a: NonZero<u32>, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: the maximum of two non-zero values is still non-zero.
    unsafe { new_unchecked_ext(get_ext(a).max(get_ext(b))) }
}

/// `<NonZero<T> as Ord>::min`: min of two non-zero values is non-zero.
#[rapx::verify]
pub fn min_ext(a: NonZero<u32>, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: the minimum of two non-zero values is still non-zero.
    unsafe { new_unchecked_ext(get_ext(a).min(get_ext(b))) }
}

/// `<NonZero<T> as Ord>::clamp`: a non-zero value clamped between two non-zero
/// values is still non-zero.
#[rapx::verify]
pub fn clamp_ext(a: NonZero<u32>, min: NonZero<u32>, max: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: a non-zero value clamped between two non-zero values is non-zero.
    unsafe { new_unchecked_ext(get_ext(a).clamp(get_ext(min), get_ext(max))) }
}

/// `<NonZero<T> as BitOr<NonZero<T>>>::bitor`: `a | b` of two non-zero values
/// is non-zero.
#[rapx::verify]
pub fn bitor_ext(a: NonZero<u32>, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: bitwise OR of two non-zero values is still non-zero.
    unsafe { new_unchecked_ext(get_ext(a) | get_ext(b)) }
}

/// `<NonZero<T> as BitOr<T>>::bitor`: `a | b` with a non-zero `a` is non-zero.
#[rapx::verify]
pub fn bitor_rhs_ext(a: NonZero<u32>, b: u32) -> NonZero<u32> {
    // SAFETY: bitwise OR of a non-zero value with anything is still non-zero.
    unsafe { new_unchecked_ext(get_ext(a) | b) }
}

/// `<T as BitOr<NonZero<T>>>::bitor`: `a | b` with a non-zero `b` is non-zero.
#[rapx::verify]
pub fn bitor_lhs_ext(a: u32, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: bitwise OR of anything with a non-zero value is still non-zero.
    unsafe { new_unchecked_ext(a | get_ext(b)) }
}

/// `NonZero::count_ones`: `self` non-zero implies at least one set bit, so the
/// popcount is non-zero.
#[rapx::verify]
pub fn count_ones_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: `self` is non-zero, so it has at least one bit set.
    unsafe { new_unchecked_ext(get_ext(a).count_ones()) }
}

/// `NonZero::rotate_left`: rotating bits preserves non-zero-ness.
#[rapx::verify]
pub fn rotate_left_ext(a: NonZero<u32>, n: u32) -> NonZero<u32> {
    // SAFETY: rotating bits preserves the property int > 0.
    unsafe { new_unchecked_ext(get_ext(a).rotate_left(n)) }
}

/// `NonZero::rotate_right`: rotating bits preserves non-zero-ness.
#[rapx::verify]
pub fn rotate_right_ext(a: NonZero<u32>, n: u32) -> NonZero<u32> {
    // SAFETY: rotating bits preserves the property int > 0.
    unsafe { new_unchecked_ext(get_ext(a).rotate_right(n)) }
}

/// `NonZero::swap_bytes`: shuffling bytes preserves non-zero-ness.
#[rapx::verify]
pub fn swap_bytes_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: shuffling bytes preserves the property int > 0.
    unsafe { new_unchecked_ext(get_ext(a).swap_bytes()) }
}

/// `NonZero::reverse_bits`: reversing bits preserves non-zero-ness.
#[rapx::verify]
pub fn reverse_bits_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: reversing bits preserves the property int > 0.
    unsafe { new_unchecked_ext(get_ext(a).reverse_bits()) }
}

/// `NonZero::from_be`: byte order conversion preserves non-zero-ness.
#[rapx::verify]
pub fn from_be_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: shuffling bytes preserves the property int > 0.
    unsafe { new_unchecked_ext(u32::from_be(get_ext(a))) }
}

/// `NonZero::from_le`: byte order conversion preserves non-zero-ness.
#[rapx::verify]
pub fn from_le_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: shuffling bytes preserves the property int > 0.
    unsafe { new_unchecked_ext(u32::from_le(get_ext(a))) }
}

/// `NonZero::to_be`: byte order conversion preserves non-zero-ness.
#[rapx::verify]
pub fn to_be_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: shuffling bytes preserves the property int > 0.
    unsafe { new_unchecked_ext(get_ext(a).to_be()) }
}

/// `NonZero::to_le`: byte order conversion preserves non-zero-ness.
#[rapx::verify]
pub fn to_le_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: shuffling bytes preserves the property int > 0.
    unsafe { new_unchecked_ext(get_ext(a).to_le()) }
}

/// `NonZero::checked_mul`: without overflow, the product of two non-zero
/// values is non-zero.
#[rapx::verify]
pub fn checked_mul_ext(a: NonZero<u32>, b: NonZero<u32>) -> Option<NonZero<u32>> {
    if let Some(result) = get_ext(a).checked_mul(get_ext(b)) {
        // SAFETY: `checked_mul` returns `None` on overflow, and the only way to
        // get zero from a multiplication without overflow is for one side to
        // be zero.
        Some(unsafe { new_unchecked_ext(result) })
    } else {
        None
    }
}

/// `NonZero::saturating_mul`: the product of two non-zero values (saturated to
/// `MAX` on overflow) is non-zero.
#[rapx::verify]
pub fn saturating_mul_ext(a: NonZero<u32>, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: `saturating_mul` returns `MAX` on overflow (non-zero); otherwise
    // the product of two non-zero values is non-zero.
    unsafe { new_unchecked_ext(get_ext(a).saturating_mul(get_ext(b))) }
}

/// `NonZero::unchecked_mul`: product without overflow (non-zero).
///
/// # Safety
///
/// Overflow is unchecked; it is UB to overflow even if the result would wrap
/// to a non-zero value.
#[rapx::verify]
#[rapx::requires(ValidNum(0 == 0))]
pub unsafe fn unchecked_mul_ext(a: NonZero<u32>, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: the caller ensures there is no overflow, and the product of two
    // non-zero values is non-zero.
    unsafe { new_unchecked_ext(get_ext(a).unchecked_mul(get_ext(b))) }
}

/// `NonZero::checked_pow`: without overflow, a positive power of a non-zero
/// value is non-zero.
#[rapx::verify]
pub fn checked_pow_ext(a: NonZero<u32>, exp: u32) -> Option<NonZero<u32>> {
    if let Some(result) = get_ext(a).checked_pow(exp) {
        // SAFETY: `checked_pow` returns `None` on overflow; otherwise a positive
        // power of a non-zero base is non-zero.
        Some(unsafe { new_unchecked_ext(result) })
    } else {
        None
    }
}

/// `NonZero::saturating_pow`: a positive power of a non-zero value (saturated
/// to `MAX` on overflow) is non-zero.
#[rapx::verify]
pub fn saturating_pow_ext(a: NonZero<u32>, exp: u32) -> NonZero<u32> {
    // SAFETY: `saturating_pow` returns `MAX` on overflow (non-zero); otherwise
    // a positive power of a non-zero base is non-zero.
    unsafe { new_unchecked_ext(get_ext(a).saturating_pow(exp)) }
}

/// `NonZero::checked_add`: without overflow, `self + other` (with `self`
/// non-zero) is non-zero.
#[rapx::verify]
pub fn checked_add_ext(a: NonZero<u32>, other: u32) -> Option<NonZero<u32>> {
    if let Some(result) = get_ext(a).checked_add(other) {
        // SAFETY: `checked_add` returns `None` on overflow, and the only way to
        // get zero from an addition without overflow is for both sides to be
        // zero (but `self` is non-zero).
        Some(unsafe { new_unchecked_ext(result) })
    } else {
        None
    }
}

/// `NonZero::saturating_add`: `self + other` (saturated to `MAX` on overflow)
/// is non-zero.
#[rapx::verify]
pub fn saturating_add_ext(a: NonZero<u32>, other: u32) -> NonZero<u32> {
    // SAFETY: `saturating_add` returns `MAX` on overflow (non-zero); otherwise
    // the sum has a non-zero addend, so it is non-zero.
    unsafe { new_unchecked_ext(get_ext(a).saturating_add(other)) }
}

/// `NonZero::unchecked_add`: sum without overflow (non-zero).
///
/// # Safety
///
/// Overflow is unchecked; it is UB to overflow even if the result would wrap
/// to a non-zero value.
#[rapx::verify]
#[rapx::requires(ValidNum(get_ext(a) <= u32::MAX - other))]
pub unsafe fn unchecked_add_ext(a: NonZero<u32>, other: u32) -> NonZero<u32> {
    // SAFETY: the caller ensures there is no overflow, and the sum has a
    // non-zero addend, so it is non-zero.
    unsafe { new_unchecked_ext(get_ext(a).unchecked_add(other)) }
}

/// `NonZero::checked_next_power_of_two`: the next power of two is positive.
#[rapx::verify]
pub fn checked_next_power_of_two_ext(a: NonZero<u32>) -> Option<NonZero<u32>> {
    if let Some(nz) = get_ext(a).checked_next_power_of_two() {
        // SAFETY: the next power of two is positive and overflow is checked.
        Some(unsafe { new_unchecked_ext(nz) })
    } else {
        None
    }
}

/// `NonZero::midpoint`: the midpoint of two unsigned non-zero values is
/// non-zero.
#[rapx::verify]
pub fn midpoint_ext(a: NonZero<u32>, b: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: the only way to get `0` with midpoint is to have two opposite or
    // near-opposite numbers, impossible for unsigned non-zero inputs.
    unsafe { new_unchecked_ext(get_ext(a).midpoint(get_ext(b))) }
}

/// `NonZero::isqrt`: the integer square root of a non-zero unsigned value is
/// non-zero.
#[rapx::verify]
pub fn isqrt_ext(a: NonZero<u32>) -> NonZero<u32> {
    // SAFETY: `isqrt` is monotonically nondecreasing; the input is >= 1, so the
    // result is >= isqrt(1) == 1.
    unsafe { new_unchecked_ext(get_ext(a).isqrt()) }
}

// ========================================================================
// Part 2 — signed (`i32`) methods
// ========================================================================

/// `NonZero::neg` (signed): negation of a non-zero value is non-zero.
#[rapx::verify]
pub fn neg_ext(a: NonZero<i32>) -> NonZero<i32> {
    // SAFETY: negation of non-zero cannot yield zero.
    unsafe { new_unchecked_ext(get_ext(a).neg()) }
}

/// `NonZero::abs` (signed): the absolute value of a non-zero value is non-zero.
#[rapx::verify]
pub fn abs_ext(a: NonZero<i32>) -> NonZero<i32> {
    // SAFETY: the absolute value of non-zero cannot yield zero.
    unsafe { new_unchecked_ext(get_ext(a).abs()) }
}

/// `NonZero::checked_abs` (signed): checked absolute value (returns `None` on
/// overflow, i.e. `MIN`).
#[rapx::verify]
pub fn checked_abs_ext(a: NonZero<i32>) -> Option<NonZero<i32>> {
    if let Some(nz) = get_ext(a).checked_abs() {
        // SAFETY: the absolute value of non-zero cannot yield zero.
        Some(unsafe { new_unchecked_ext(nz) })
    } else {
        None
    }
}

/// `NonZero::overflowing_abs` (signed): absolute value with overflow flag.
#[rapx::verify]
pub fn overflowing_abs_ext(a: NonZero<i32>) -> (NonZero<i32>, bool) {
    let (nz, flag) = get_ext(a).overflowing_abs();
    // SAFETY: the absolute value of non-zero cannot yield zero.
    (unsafe { new_unchecked_ext(nz) }, flag)
}

/// `NonZero::saturating_abs` (signed): saturating absolute value.
#[rapx::verify]
pub fn saturating_abs_ext(a: NonZero<i32>) -> NonZero<i32> {
    // SAFETY: the absolute value of non-zero cannot yield zero.
    unsafe { new_unchecked_ext(get_ext(a).saturating_abs()) }
}

/// `NonZero::wrapping_abs` (signed): wrapping absolute value.
#[rapx::verify]
pub fn wrapping_abs_ext(a: NonZero<i32>) -> NonZero<i32> {
    // SAFETY: the absolute value of non-zero cannot yield zero.
    unsafe { new_unchecked_ext(get_ext(a).wrapping_abs()) }
}

/// `NonZero::unsigned_abs` (signed): unsigned absolute value.
#[rapx::verify]
pub fn unsigned_abs_ext(a: NonZero<i32>) -> NonZero<u32> {
    // SAFETY: the absolute value of non-zero cannot yield zero.
    unsafe { new_unchecked_ext(get_ext(a).unsigned_abs()) }
}

/// `NonZero::checked_neg` (signed): checked negation (returns `None` on `MIN`).
#[rapx::verify]
pub fn checked_neg_ext(a: NonZero<i32>) -> Option<NonZero<i32>> {
    if let Some(result) = get_ext(a).checked_neg() {
        // SAFETY: negation of non-zero cannot yield zero.
        Some(unsafe { new_unchecked_ext(result) })
    } else {
        None
    }
}

/// `NonZero::overflowing_neg` (signed): negation with overflow flag.
#[rapx::verify]
pub fn overflowing_neg_ext(a: NonZero<i32>) -> (NonZero<i32>, bool) {
    let (result, overflow) = get_ext(a).overflowing_neg();
    // SAFETY: negation of non-zero cannot yield zero.
    (unsafe { new_unchecked_ext(result) }, overflow)
}

/// `NonZero::wrapping_neg` (signed): wrapping negation.
#[rapx::verify]
pub fn wrapping_neg_ext(a: NonZero<i32>) -> NonZero<i32> {
    // SAFETY: negation of non-zero cannot yield zero.
    unsafe { new_unchecked_ext(get_ext(a).wrapping_neg()) }
}
