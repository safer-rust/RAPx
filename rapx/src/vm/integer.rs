//! Pure finite-width integer semantics at the boundary of the Int-based VM.
//!
//! Stored integer terms are the mathematical interpretation of machine values,
//! including negative signed values. Bit vectors are local to bitwise operations.

use z3::{
    Context, DeclKind,
    ast::{Ast, BV, Bool, Int},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct IntLayout {
    pub(crate) bits: u16,
    pub(crate) signed: bool,
}

impl IntLayout {
    pub(crate) fn new(bits: u16, signed: bool) -> Option<Self> {
        (1..=128).contains(&bits).then_some(Self { bits, signed })
    }

    pub(crate) fn min<'z3>(self, ctx: &'z3 Context) -> Int<'z3> {
        if self.signed {
            let minimum = if self.bits == 128 {
                i128::MIN
            } else {
                -(1_i128 << (self.bits - 1))
            };
            Int::from_str(ctx, &minimum.to_string()).expect("integer numeral")
        } else {
            Int::from_u64(ctx, 0)
        }
    }

    pub(crate) fn max<'z3>(self, ctx: &'z3 Context) -> Int<'z3> {
        let maximum = if self.signed {
            (1_u128 << (self.bits - 1)) - 1
        } else if self.bits == 128 {
            u128::MAX
        } else {
            (1_u128 << self.bits) - 1
        };
        Int::from_str(ctx, &maximum.to_string()).expect("integer numeral")
    }

    pub(crate) fn modulus<'z3>(self, ctx: &'z3 Context) -> Int<'z3> {
        let unsigned = Self {
            signed: false,
            ..self
        };
        Int::add(ctx, &[&unsigned.max(ctx), &Int::from_u64(ctx, 1)])
    }

    /// Interpret the low `bits` bits of an arbitrary mathematical integer.
    pub(crate) fn normalize<'z3>(self, ctx: &'z3 Context, raw: &Int<'z3>) -> Int<'z3> {
        let modulus = self.modulus(ctx);
        let wrapped = raw.modulo(&modulus);
        if self.signed {
            wrapped
                .gt(&self.max(ctx))
                .ite(&Int::sub(ctx, &[&wrapped, &modulus]), &wrapped)
        } else {
            wrapped
        }
    }

    pub(crate) fn in_domain<'z3>(self, ctx: &'z3 Context, value: &Int<'z3>) -> Bool<'z3> {
        let magnitude_bits = self.bits - u16::from(self.signed);
        if natural_upper_bound(value, 5)
            .is_some_and(|bound| magnitude_bits == 128 || bound < (1_u128 << magnitude_bits))
        {
            return Bool::from_bool(ctx, true);
        }
        Bool::and(ctx, &[&value.ge(&self.min(ctx)), &value.le(&self.max(ctx))])
    }

    /// Decode a scalar's bit pattern, including the full 128-bit range.
    pub(crate) fn from_bits<'z3>(self, ctx: &'z3 Context, bits: u128) -> Int<'z3> {
        self.normalize(ctx, &u128_term(ctx, bits)).simplify()
    }

    pub(crate) fn bitnot<'z3>(self, ctx: &'z3 Context, value: &Int<'z3>) -> Int<'z3> {
        // The complement of a signed value is -1 - x, including for MIN.
        let all_ones = if self.signed {
            Int::from_i64(ctx, -1)
        } else {
            self.max(ctx)
        };
        Int::sub(ctx, &[&all_ones, &self.normalize(ctx, value)])
    }

    pub(crate) fn bitwise<'z3>(
        self,
        ctx: &'z3 Context,
        op: BitwiseOp,
        lhs: &Int<'z3>,
        rhs: &Int<'z3>,
    ) -> Int<'z3> {
        if let Some((value, mask)) = numeral_bits(rhs)
            .map(|mask| (lhs, mask))
            .or_else(|| numeral_bits(lhs).map(|mask| (rhs, mask)))
            && let Some(term) = self.bitwise_constant(ctx, op, value, mask)
        {
            return term;
        }
        let left = BV::from_int(lhs, u32::from(self.bits));
        let right = BV::from_int(rhs, u32::from(self.bits));
        match op {
            BitwiseOp::And => left.bvand(&right),
            BitwiseOp::Or => left.bvor(&right),
            BitwiseOp::Xor => left.bvxor(&right),
        }
        .to_int(self.signed)
    }

    /// Extract the bit runs selected by the constant mask using Int residues.
    /// The run containing the sign bit uses its signed positional weights.
    /// Masks with many runs keep the compact BV encoding.
    fn bitwise_constant<'z3>(
        self,
        ctx: &'z3 Context,
        op: BitwiseOp,
        value: &Int<'z3>,
        mask: u128,
    ) -> Option<Int<'z3>> {
        let word_mask = u128::MAX >> (128 - self.bits);
        let mask = mask & word_mask;
        if mask == 0 {
            return Some(match op {
                BitwiseOp::And => Int::from_u64(ctx, 0),
                _ => self.normalize(ctx, value),
            });
        }
        if mask == word_mask {
            return Some(match op {
                BitwiseOp::And => self.normalize(ctx, value),
                BitwiseOp::Or => self.from_bits(ctx, mask),
                BitwiseOp::Xor => self.bitnot(ctx, value),
            });
        }
        if !matches!(op, BitwiseOp::And) || (mask & !(mask << 1)).count_ones() > 2 {
            return None;
        }

        let mut runs = Vec::new();
        let mut remaining = mask;
        while remaining != 0 {
            let start = remaining.trailing_zeros();
            let width = (remaining >> start).trailing_ones();
            let run_mask = (u128::MAX >> (128 - width)) << start;
            remaining &= !run_mask;
            let stride = u128_term(ctx, 1_u128 << start);
            let end = start + width;
            let run = if end == u32::from(self.bits) {
                // The discarded low bits have the same residue before and
                // after word normalization, including on signed words.
                Int::sub(ctx, &[&self.normalize(ctx, value), &value.modulo(&stride)])
            } else {
                let residue = value.modulo(&u128_term(ctx, 1_u128 << end));
                if start == 0 {
                    residue
                } else if width == 1 {
                    residue.ge(&stride).ite(&stride, &Int::from_u64(ctx, 0))
                } else {
                    Int::sub(ctx, &[&residue, &value.modulo(&stride)])
                }
            };
            runs.push(run);
        }
        Some(Int::add(ctx, &runs.iter().collect::<Vec<_>>()))
    }

    /// A bitwise AND with a constant mask clears its trailing zero bits in
    /// every result. Return the corresponding power-of-two divisor when it
    /// fits in `u64`. This fact supplements the exact bitwise result.
    pub(crate) fn bitand_multiple<'z3>(self, ctx: &'z3 Context, mask: &Int<'z3>) -> Option<Int<'z3>> {
        let bits = mask.simplify().as_u64()?;
        let zeros = bits.trailing_zeros().min(u32::from(self.bits));
        (zeros > 0 && zeros < 64).then(|| Int::from_u64(ctx, 1_u64 << zeros))
    }
}

fn numeral_bits(value: &Int<'_>) -> Option<u128> {
    let value = value.simplify();
    if let Some(unsigned) = value.as_u64() {
        return Some(u128::from(unsigned));
    }
    if let Some(signed) = value.as_i64() {
        return Some(i128::from(signed) as u128);
    }
    if value.decl().kind() == DeclKind::ANUM {
        return value.to_string().parse().ok();
    }
    None
}

fn unsigned_bitvector<'z3>(value: &Int<'z3>) -> Option<BV<'z3>> {
    if value.decl().kind() != DeclKind::BV2INT {
        return None;
    }
    value.nth_child(0)?.as_bv()
}

/// A syntactic bound for terms that are already nonnegative by construction.
/// This keeps redundant Int inequalities out of queries over bitwise terms.
pub(crate) fn natural_upper_bound(value: &Int<'_>, depth: usize) -> Option<u128> {
    if depth == 0 {
        return None;
    }
    let child = |index| value.nth_child(index)?.as_int();
    match value.decl().kind() {
        DeclKind::ANUM => value
            .as_u64()
            .map(u128::from)
            .or_else(|| value.to_string().parse().ok()),
        DeclKind::BV2INT => {
            let width = unsigned_bitvector(value)?.get_size();
            (1..=128).contains(&width).then(|| u128::MAX >> (128 - width))
        }
        DeclKind::MOD => {
            let divisor = child(1)?;
            let divisor = divisor.simplify();
            if divisor.decl().kind() != DeclKind::ANUM {
                return None;
            }
            divisor
                .as_u64()
                .map(u128::from)
                .or_else(|| divisor.to_string().parse().ok())?
                .checked_sub(1)
        }
        DeclKind::ADD | DeclKind::MUL => {
            let product = value.decl().kind() == DeclKind::MUL;
            (0..value.num_children()).try_fold(u128::from(product), |acc, index| {
                let bound = natural_upper_bound(&child(index)?, depth - 1)?;
                if product {
                    acc.checked_mul(bound)
                } else {
                    acc.checked_add(bound)
                }
            })
        }
        DeclKind::ITE => {
            let yes = natural_upper_bound(&child(1)?, depth - 1)?;
            let no = natural_upper_bound(&child(2)?, depth - 1)?;
            Some(yes.max(no))
        }
        _ => None,
    }
}

/// A zero test on an unsigned BV-to-Int conversion is a BV equality. Keeping
/// it in BV avoids introducing integer arithmetic for a bitwise result.
pub(crate) fn integer_eq<'z3>(lhs: &Int<'z3>, rhs: &Int<'z3>) -> Bool<'z3> {
    let bv = if rhs.as_u64() == Some(0) {
        unsigned_bitvector(lhs)
    } else if lhs.as_u64() == Some(0) {
        unsigned_bitvector(rhs)
    } else {
        None
    };
    match bv {
        Some(bits) => bits._eq(&BV::from_u64(bits.get_ctx(), 0, bits.get_size())),
        None => lhs._eq(rhs),
    }
}

/// Select a numeric conditional arm when the VM already asserted its guard.
/// Checked arithmetic flags can appear in constraints as Boolean values or
/// as an equality on the corresponding MIR 0/1 representation.
pub(crate) fn known_ite_arm<'z3>(term: &Int<'z3>, assertions: &[Bool<'z3>]) -> Option<Int<'z3>> {
    if term.decl().kind() != DeclKind::ITE {
        return None;
    }
    let guard = term.nth_child(0)?.as_bool()?;
    let not_guard = guard.not();
    let zero = Int::from_u64(term.get_ctx(), 0);
    let flag_is_zero = guard.ite(&Int::from_u64(term.get_ctx(), 1), &zero)._eq(&zero);
    let flag_is_one = flag_is_zero.not();
    for assertion in assertions.iter().rev() {
        if *assertion == guard || *assertion == flag_is_one {
            return term.nth_child(1)?.as_int();
        }
        if *assertion == not_guard || *assertion == flag_is_zero {
            return term.nth_child(2)?.as_int();
        }
    }
    None
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum BitwiseOp {
    And,
    Or,
    Xor,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum AddSubMul {
    Add,
    Sub,
    Mul,
}

pub(crate) struct OverflowResult<'z3> {
    pub(crate) value: Int<'z3>,
    pub(crate) overflow: Bool<'z3>,
}

pub(crate) fn overflowing_binary<'z3>(
    ctx: &'z3 Context,
    layout: IntLayout,
    op: AddSubMul,
    lhs: &Int<'z3>,
    rhs: &Int<'z3>,
) -> OverflowResult<'z3> {
    let raw = match op {
        AddSubMul::Add => Int::add(ctx, &[lhs, rhs]),
        AddSubMul::Sub => Int::sub(ctx, &[lhs, rhs]),
        AddSubMul::Mul => Int::mul(ctx, &[lhs, rhs]),
    };
    let overflow = layout.in_domain(ctx, &raw).not().simplify();
    // Expose the unwrapped result on the no-overflow arm. A MIR overflow
    // assertion can then eliminate the expensive word-size remainder.
    let value = match overflow.as_bool() {
        Some(false) => raw,
        Some(true) => layout.normalize(ctx, &raw).simplify(),
        None => overflow.ite(&layout.normalize(ctx, &raw), &raw),
    };
    OverflowResult { value, overflow }
}

/// Rust signed division rounds toward zero; the remainder follows the dividend.
///
/// The caller handles division by zero and `MIN / -1` / `MIN % -1` definedness.
/// This helper adds no assumptions and does not normalize an invalid quotient.
pub(crate) fn signed_div_rem<'z3>(
    ctx: &'z3 Context,
    lhs: &Int<'z3>,
    rhs: &Int<'z3>,
) -> (Int<'z3>, Int<'z3>) {
    let zero = Int::from_u64(ctx, 0);
    let lhs_negative = lhs.lt(&zero);
    let rhs_negative = rhs.lt(&zero);
    let lhs_abs = lhs_negative.ite(&(-lhs.clone()), lhs);
    let rhs_abs = rhs_negative.ite(&(-rhs.clone()), rhs);
    let magnitude = lhs_abs.div(&rhs_abs);
    let quotient = lhs_negative
        .xor(&rhs_negative)
        .ite(&(-magnitude.clone()), &magnitude);
    let remainder = Int::sub(ctx, &[lhs, &Int::mul(ctx, &[&quotient, rhs])]);
    (quotient, remainder)
}

pub(crate) fn u128_term<'z3>(ctx: &'z3 Context, value: u128) -> Int<'z3> {
    let low = Int::from_u64(ctx, value as u64);
    if value <= u64::MAX as u128 {
        return low;
    }
    let high = Int::from_u64(ctx, (value >> 64) as u64);
    let two_64 = Int::add(
        ctx,
        &[&Int::from_u64(ctx, u64::MAX), &Int::from_u64(ctx, 1)],
    );
    Int::add(ctx, &[&Int::mul(ctx, &[&high, &two_64]), &low])
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::{Config, SatResult, Solver};

    fn extend<'z3>(value: &BV<'z3>, width: u16, signed: bool) -> BV<'z3> {
        if signed {
            value.sign_ext(u32::from(width))
        } else {
            value.zero_ext(u32::from(width))
        }
    }

    fn reference_binary<'z3>(op: AddSubMul, lhs: &BV<'z3>, rhs: &BV<'z3>) -> BV<'z3> {
        match op {
            AddSubMul::Add => lhs.bvadd(rhs),
            AddSubMul::Sub => lhs.bvsub(rhs),
            AddSubMul::Mul => lhs.bvmul(rhs),
        }
    }

    fn assert_realizable(solver: &Solver<'_>, relation: &Bool<'_>, case: &str) {
        // Check coverage directly. An inconsistent model must fail this test,
        // rather than make an implication to the reference result vacuous.
        solver.push();
        solver.assert(relation);
        assert_eq!(solver.check(), SatResult::Sat, "{case}: {relation}");
        solver.pop(1);
    }

    #[test]
    fn layout_rejects_invalid_widths() {
        assert!(IntLayout::new(0, false).is_none());
        assert!(IntLayout::new(129, true).is_none());
        assert!(IntLayout::new(u16::MAX, false).is_none());
        assert!(IntLayout::new(1, true).is_some());
        assert!(IntLayout::new(128, false).is_some());
    }

    #[test]
    fn exhaustive_small_overflow_matches_widened_bitvectors() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        for width in [3_u16, 4] {
            for signed in [false, true] {
                let layout = IntLayout::new(width, signed).unwrap();
                for left_bits in 0..(1_u64 << width) {
                    for right_bits in 0..(1_u64 << width) {
                        let left = BV::from_u64(&ctx, left_bits, u32::from(width));
                        let right = BV::from_u64(&ctx, right_bits, u32::from(width));
                        for op in [AddSubMul::Add, AddSubMul::Sub, AddSubMul::Mul] {
                            let expected = reference_binary(op, &left, &right);
                            let widened = reference_binary(
                                op,
                                &extend(&left, width, signed),
                                &extend(&right, width, signed),
                            );
                            let expected_overflow =
                                widened._eq(&extend(&expected, width, signed)).not();
                            let actual = overflowing_binary(
                                &ctx,
                                layout,
                                op,
                                &left.to_int(signed),
                                &right.to_int(signed),
                            );
                            let relation = Bool::and(
                                &ctx,
                                &[
                                    &actual.value._eq(&expected.to_int(signed)),
                                    &actual.overflow._eq(&expected_overflow),
                                    &layout.in_domain(&ctx, &actual.value),
                                ],
                            );
                            assert_realizable(
                                &solver,
                                &relation,
                                &format!("{layout:?} {op:?} {left_bits} {right_bits}"),
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn casts_match_bitvector_truncation_and_extension() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        for source_width in [3_u16, 4, 8, 16, 32, 64, 128] {
            let mask = u128::MAX >> (128 - source_width);
            let sign_bit = 1_u128 << (source_width - 1);
            let samples = if source_width <= 4 {
                (0..=mask).collect::<Vec<_>>()
            } else {
                vec![0, 1, sign_bit - 1, sign_bit, mask - 1, mask]
            };
            for source_signed in [false, true] {
                for bits in &samples {
                    let source =
                        BV::from_str(&ctx, u32::from(source_width), &bits.to_string()).unwrap();
                    for destination_width in [1_u16, 3, 4, 8, 16, 32, 64, 128] {
                        let expected_bits = if destination_width < source_width {
                            source.extract(u32::from(destination_width - 1), 0)
                        } else if source_signed {
                            source.sign_ext(u32::from(destination_width - source_width))
                        } else {
                            source.zero_ext(u32::from(destination_width - source_width))
                        };
                        for destination_signed in [false, true] {
                            let layout =
                                IntLayout::new(destination_width, destination_signed).unwrap();
                            let actual = layout.normalize(&ctx, &source.to_int(source_signed));
                            assert_realizable(
                                &solver,
                                &actual._eq(&expected_bits.to_int(destination_signed)),
                                &format!(
                                    "cast {source_width}/{source_signed} {bits} to {layout:?}"
                                ),
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn bitpatterns_and_not_cover_128_bit_boundaries() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        for width in [1_u16, 3, 4, 8, 16, 32, 64, 128] {
            let mask = u128::MAX >> (128 - width);
            let high_bit = 1_u128 << (width - 1);
            for signed in [false, true] {
                let layout = IntLayout::new(width, signed).unwrap();
                let reference = |bits: u128| {
                    let bits = bits & mask;
                    let value = if signed && bits & high_bit != 0 {
                        // Native signed sign extension is independent of the
                        // kernel's Int modulo and BV conversion encodings.
                        (((bits << (128 - width)) as i128) >> (128 - width)).to_string()
                    } else {
                        bits.to_string()
                    };
                    Int::from_str(&ctx, &value).unwrap()
                };
                for bits in [0, 1, high_bit - 1, high_bit, mask, u128::MAX] {
                    let actual = layout.from_bits(&ctx, bits);
                    let agreement = Bool::and(
                        &ctx,
                        &[
                            &actual._eq(&reference(bits)),
                            &layout.bitnot(&ctx, &actual)._eq(&reference(!bits)),
                            &layout.in_domain(&ctx, &actual),
                        ],
                    );
                    assert_realizable(&solver, &agreement, &format!("{layout:?} bits={bits}"));
                }
            }
        }
        let unsigned = IntLayout::new(128, false).unwrap();
        let signed = IntLayout::new(128, true).unwrap();
        assert_realizable(
            &solver,
            &unsigned
                .modulus(&ctx)
                ._eq(&Int::from_str(&ctx, "340282366920938463463374607431768211456").unwrap()),
            "2^128 modulus",
        );
        assert_realizable(
            &solver,
            &signed
                .min(&ctx)
                ._eq(&Int::from_str(&ctx, &i128::MIN.to_string()).unwrap()),
            "i128 minimum",
        );
    }

    #[test]
    fn exhaustive_small_signed_division_matches_bitvectors() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        for width in [3_u16, 4] {
            for left_bits in 0..(1_u64 << width) {
                for right_bits in 1..(1_u64 << width) {
                    // Rust rejects MIN / -1 and MIN % -1. The adapter owns
                    // those definedness conditions, not this arithmetic helper.
                    if left_bits == 1_u64 << (width - 1) && right_bits == (1_u64 << width) - 1 {
                        continue;
                    }
                    let left = BV::from_u64(&ctx, left_bits, u32::from(width));
                    let right = BV::from_u64(&ctx, right_bits, u32::from(width));
                    let (quotient, remainder) =
                        signed_div_rem(&ctx, &left.to_int(true), &right.to_int(true));
                    let agreement = Bool::and(
                        &ctx,
                        &[
                            &quotient._eq(&left.bvsdiv(&right).to_int(true)),
                            &remainder._eq(&left.bvsrem(&right).to_int(true)),
                        ],
                    );
                    assert_realizable(
                        &solver,
                        &agreement,
                        &format!("signed {width}-bit division {left_bits}/{right_bits}"),
                    );
                }
            }
        }
    }

    #[test]
    fn bitwise_matches_native_small_integer_patterns() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        for width in [3_u16, 4] {
            for signed in [false, true] {
                let layout = IntLayout::new(width, signed).unwrap();
                for left in 0..(1_u64 << width) {
                    for right in 0..(1_u64 << width) {
                        for op in [BitwiseOp::And, BitwiseOp::Or, BitwiseOp::Xor] {
                            let reference_bits = match op {
                                BitwiseOp::And => left & right,
                                BitwiseOp::Or => left | right,
                                BitwiseOp::Xor => left ^ right,
                            };
                            let expected =
                                BV::from_u64(&ctx, reference_bits, u32::from(width)).to_int(signed);
                            let actual = layout.bitwise(
                                &ctx,
                                op,
                                &layout.from_bits(&ctx, u128::from(left)),
                                &layout.from_bits(&ctx, u128::from(right)),
                            );
                            assert_realizable(
                                &solver,
                                &actual._eq(&expected),
                                &format!("{layout:?} {op:?} {left} {right}"),
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn checked_result_specializes_only_with_an_asserted_flag() {
        let ctx = Context::new(&Config::new());
        let layout = IntLayout::new(8, false).unwrap();
        let x = Int::new_const(&ctx, "x");
        let one = Int::from_u64(&ctx, 1);
        let zero = Int::from_u64(&ctx, 0);
        let raw = Int::add(&ctx, &[&x, &one]);
        let result = overflowing_binary(&ctx, layout, AddSubMul::Add, &x, &one);
        assert!(known_ite_arm(&result.value, &[]).is_none());

        let flag_is_zero = result.overflow.ite(&one, &zero)._eq(&zero);
        assert_eq!(
            known_ite_arm(&result.value, &[flag_is_zero.clone()]),
            Some(raw.clone())
        );
        assert_eq!(
            known_ite_arm(&result.value, &[flag_is_zero.not()]),
            Some(layout.normalize(&ctx, &raw))
        );
    }

    #[test]
    fn constant_masks_match_bv_at_word_boundaries() {
        let ctx = Context::new(&Config::new());
        for width in [8, 64, 128] {
            for signed in [false, true] {
                let layout = IntLayout::new(width, signed).unwrap();
                let sign_bit = 1_u128 << (width - 1);
                for mask in [0, 1, 8, 0b10110, !7, sign_bit, sign_bit | 7, u128::MAX] {
                    let mask_term = layout.from_bits(&ctx, mask);
                    for value in [
                        Int::from_i64(&ctx, -257),
                        Int::from_u64(&ctx, 0),
                        u128_term(&ctx, sign_bit + 1),
                        u128_term(&ctx, u128::MAX),
                    ] {
                        let bits = BV::from_int(&value, u32::from(width));
                        let mask_bits = BV::from_int(&mask_term, u32::from(width));
                        let actual = layout.bitwise(&ctx, BitwiseOp::And, &value, &mask_term);
                        assert_eq!(
                            actual.simplify(),
                            bits.bvand(&mask_bits).to_int(signed).simplify()
                        );
                        assert_eq!(
                            layout.bitnot(&ctx, &value).simplify(),
                            bits.bvnot().to_int(signed).simplify()
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn bitvector_zero_test_preserves_integer_equality() {
        let ctx = Context::new(&Config::new());
        let bits = BV::new_const(&ctx, "bits", 4);
        let zero = Int::from_u64(&ctx, 0);
        let solver = Solver::new(&ctx);
        for signed in [false, true] {
            let number = bits.to_int(signed);
            solver.push();
            solver.assert(&integer_eq(&number, &zero).xor(&number._eq(&zero)));
            assert_eq!(solver.check(), SatResult::Unsat);
            solver.pop(1);
        }
        assert_eq!(natural_upper_bound(&bits.to_int(false), 5), Some(15));
        assert!(natural_upper_bound(&bits.to_int(true), 5).is_none());
        assert!(natural_upper_bound(&bits.to_int(false).modulo(&zero), 5).is_none());
    }

    #[test]
    fn bitand_alignment_fact_follows_from_machine_bits() {
        let ctx = Context::new(&Config::new());
        let small = IntLayout::new(8, false).unwrap();
        let small_mask = small.from_bits(&ctx, 0xf8);
        let multiple = small.bitand_multiple(&ctx, &small_mask).unwrap();
        assert_eq!(multiple.as_u64(), Some(8));
        let input = Int::new_const(&ctx, "input_8");
        let result = small.bitwise(&ctx, BitwiseOp::And, &input, &small_mask);
        let solver = Solver::new(&ctx);
        solver.assert(&small.in_domain(&ctx, &input));
        solver.assert(&result.rem(&multiple)._eq(&Int::from_u64(&ctx, 0)).not());
        assert_eq!(solver.check(), SatResult::Unsat);

        let wide = IntLayout::new(64, false).unwrap();
        let wide_mask = wide.from_bits(&ctx, u128::from(u64::MAX - 7));
        let wide_multiple = wide.bitand_multiple(&ctx, &wide_mask).unwrap();
        assert_eq!(wide_multiple.as_u64(), Some(8));
        for bits in [0, 1, 7, 8, u64::MAX - 1, u64::MAX] {
            let value = wide.from_bits(&ctx, u128::from(bits));
            let result = wide.bitwise(&ctx, BitwiseOp::And, &value, &wide_mask).simplify();
            assert_eq!(result.as_u64(), Some(bits & (u64::MAX - 7)));
        }
    }

    #[test]
    fn full_width_overflow_and_division_boundaries_match_native_rust() {
        let ctx = Context::new(&Config::new());
        let solver = Solver::new(&ctx);
        let signed = IntLayout::new(128, true).unwrap();
        let unsigned = IntLayout::new(128, false).unwrap();
        for lhs in [i128::MIN, i128::MIN + 1, -3, -1, 0, 1, 3, i128::MAX] {
            for rhs in [i128::MIN, -3, -1, 0, 1, 3, i128::MAX] {
                let left = Int::from_str(&ctx, &lhs.to_string()).unwrap();
                let right = Int::from_str(&ctx, &rhs.to_string()).unwrap();
                for (op, (expected, flag)) in [
                    (AddSubMul::Add, lhs.overflowing_add(rhs)),
                    (AddSubMul::Sub, lhs.overflowing_sub(rhs)),
                    (AddSubMul::Mul, lhs.overflowing_mul(rhs)),
                ] {
                    let actual = overflowing_binary(&ctx, signed, op, &left, &right);
                    let agreement = Bool::and(
                        &ctx,
                        &[
                            &actual
                                .value
                                ._eq(&Int::from_str(&ctx, &expected.to_string()).unwrap()),
                            &actual.overflow._eq(&Bool::from_bool(&ctx, flag)),
                        ],
                    );
                    assert_realizable(&solver, &agreement, &format!("i128 {lhs} {op:?} {rhs}"));
                }
                if rhs != 0 && !(lhs == i128::MIN && rhs == -1) {
                    let (quotient, remainder) = signed_div_rem(&ctx, &left, &right);
                    let agreement = Bool::and(
                        &ctx,
                        &[
                            &quotient._eq(&Int::from_str(&ctx, &(lhs / rhs).to_string()).unwrap()),
                            &remainder._eq(&Int::from_str(&ctx, &(lhs % rhs).to_string()).unwrap()),
                        ],
                    );
                    assert_realizable(&solver, &agreement, &format!("i128 {lhs} / % {rhs}"));
                }
            }
        }
        for lhs in [0_u128, 1, (1_u128 << 127) - 1, 1_u128 << 127, u128::MAX] {
            for rhs in [0_u128, 1, 2, 1_u128 << 127, u128::MAX] {
                let left = Int::from_str(&ctx, &lhs.to_string()).unwrap();
                let right = Int::from_str(&ctx, &rhs.to_string()).unwrap();
                for (op, (expected, flag)) in [
                    (AddSubMul::Add, lhs.overflowing_add(rhs)),
                    (AddSubMul::Sub, lhs.overflowing_sub(rhs)),
                    (AddSubMul::Mul, lhs.overflowing_mul(rhs)),
                ] {
                    let actual = overflowing_binary(&ctx, unsigned, op, &left, &right);
                    let agreement = Bool::and(
                        &ctx,
                        &[
                            &actual
                                .value
                                ._eq(&Int::from_str(&ctx, &expected.to_string()).unwrap()),
                            &actual.overflow._eq(&Bool::from_bool(&ctx, flag)),
                        ],
                    );
                    assert_realizable(&solver, &agreement, &format!("u128 {lhs} {op:?} {rhs}"));
                }
            }
        }
    }
}
