use super::{need_nonzero, F32x4, I32x4, I8x16, Isizex4, MutPtrx4, Ptrx4, U32x16, Usizex4};
use core::intrinsics;

#[rapx::verify]
pub fn simd_intrinsics(value: i8) {
    let lhs = I8x16([value; 16]);
    let rhs = I8x16([0; 16]);
    let mask: I8x16 = unsafe { intrinsics::simd::simd_lt(lhs, rhs) };
    let equal: I8x16 = unsafe { intrinsics::simd::simd_eq(lhs, rhs) };
    let greater: I8x16 = unsafe { intrinsics::simd::simd_gt(lhs, rhs) };
    let added: I8x16 = unsafe { intrinsics::simd::simd_add(lhs, rhs) };
    let selected: I8x16 = unsafe { intrinsics::simd::simd_select(mask, added, lhs) };
    let selected_equal: I8x16 = unsafe { intrinsics::simd::simd_eq(selected, lhs) };
    let bits: u16 = unsafe { intrinsics::simd::simd_bitmask(mask) };
    let equal_bits: u16 = unsafe { intrinsics::simd::simd_bitmask(equal) };
    let greater_bits: u16 = unsafe { intrinsics::simd::simd_bitmask(greater) };
    let selected_bits: u16 = unsafe { intrinsics::simd::simd_bitmask(selected_equal) };
    unsafe { need_nonzero((bits ^ equal_bits ^ greater_bits ^ selected_bits) as u32) };
}

#[rapx::verify]
pub fn more_simd_intrinsics(value: i8) {
    let lhs = I8x16([value; 16]);
    let zero = I8x16([0; 16]);
    let one = I8x16([1; 16]);
    let splat: I8x16 = unsafe { intrinsics::simd::simd_splat(value) };
    let inserted = unsafe { intrinsics::simd::simd_insert(lhs, 0, value) };
    let inserted_dyn = unsafe { intrinsics::simd::simd_insert_dyn(lhs, 0, value) };
    let extracted: i8 = unsafe { intrinsics::simd::simd_extract(inserted, 0) };
    let extracted_dyn: i8 = unsafe { intrinsics::simd::simd_extract_dyn(inserted_dyn, 0) };
    let subtracted = unsafe { intrinsics::simd::simd_sub(lhs, zero) };
    let multiplied = unsafe { intrinsics::simd::simd_mul(lhs, one) };
    let divided = unsafe { intrinsics::simd::simd_div(lhs, one) };
    let remainder = unsafe { intrinsics::simd::simd_rem(lhs, one) };
    let shifted_left = unsafe { intrinsics::simd::simd_shl(lhs, zero) };
    let shifted_right = unsafe { intrinsics::simd::simd_shr(lhs, zero) };
    let anded = unsafe { intrinsics::simd::simd_and(lhs, one) };
    let ored = unsafe { intrinsics::simd::simd_or(lhs, zero) };
    let xored = unsafe { intrinsics::simd::simd_xor(lhs, zero) };
    let negated = unsafe { intrinsics::simd::simd_neg(lhs) };
    let unequal: I8x16 = unsafe { intrinsics::simd::simd_ne(lhs, zero) };
    let less_equal: I8x16 = unsafe { intrinsics::simd::simd_le(lhs, zero) };
    let greater_equal: I8x16 = unsafe { intrinsics::simd::simd_ge(lhs, zero) };
    let saturated_add = unsafe { intrinsics::simd::simd_saturating_add(lhs, one) };
    let saturated_sub = unsafe { intrinsics::simd::simd_saturating_sub(lhs, one) };
    const SHUFFLE: U32x16 = U32x16([0; 16]);
    let shuffled: I8x16 = unsafe { intrinsics::simd::simd_shuffle(lhs, zero, SHUFFLE) };
    let selected: I8x16 = unsafe { intrinsics::simd::simd_select_bitmask(0_u16, lhs, zero) };
    let total: i8 = unsafe { intrinsics::simd::simd_reduce_add_unordered(splat) };
    let maximum: i8 = unsafe { intrinsics::simd::simd_reduce_max(lhs) };
    let minimum: i8 = unsafe { intrinsics::simd::simd_reduce_min(lhs) };
    let all = unsafe { intrinsics::simd::simd_reduce_all(unequal) };
    let any = unsafe { intrinsics::simd::simd_reduce_any(less_equal) };
    let values = [
        subtracted,
        multiplied,
        divided,
        remainder,
        shifted_left,
        shifted_right,
        anded,
        ored,
        xored,
        negated,
        unequal,
        less_equal,
        greater_equal,
        saturated_add,
        saturated_sub,
        shuffled,
        selected,
    ];
    let mut result = (extracted ^ extracted_dyn ^ total ^ maximum ^ minimum) as u32;
    for vector in values {
        result ^= unsafe { intrinsics::simd::simd_extract::<_, i8>(vector, 0) } as u32;
    }
    unsafe { need_nonzero(result ^ (all as u32) ^ (any as u32)) };
}

#[rapx::verify]
pub fn simd_reduction_intrinsics(value: i8) {
    let lanes = I8x16([value; 16]);
    let leading = unsafe { intrinsics::simd::simd_ctlz(lanes) };
    let trailing = unsafe { intrinsics::simd::simd_cttz(lanes) };
    let population = unsafe { intrinsics::simd::simd_ctpop(lanes) };
    let swapped = unsafe { intrinsics::simd::simd_bswap(lanes) };
    let reversed = unsafe { intrinsics::simd::simd_bitreverse(lanes) };
    let funnel_left = unsafe { intrinsics::simd::simd_funnel_shl(lanes, lanes, I8x16([0; 16])) };
    let funnel_right = unsafe { intrinsics::simd::simd_funnel_shr(lanes, lanes, I8x16([0; 16])) };
    let carryless = unsafe { intrinsics::simd::simd_carryless_mul(lanes, I8x16([1; 16])) };
    let sum: i8 = unsafe { intrinsics::simd::simd_reduce_add_ordered(lanes, 0) };
    let product: i8 = unsafe { intrinsics::simd::simd_reduce_mul_ordered(lanes, 1) };
    let unordered_product: i8 = unsafe { intrinsics::simd::simd_reduce_mul_unordered(lanes) };
    let anded: i8 = unsafe { intrinsics::simd::simd_reduce_and(lanes) };
    let ored: i8 = unsafe { intrinsics::simd::simd_reduce_or(lanes) };
    let xored: i8 = unsafe { intrinsics::simd::simd_reduce_xor(lanes) };
    let first: i8 = unsafe { intrinsics::simd::simd_extract(leading, 0) };
    let second: i8 = unsafe { intrinsics::simd::simd_extract(trailing, 0) };
    let third: i8 = unsafe { intrinsics::simd::simd_extract(population, 0) };
    let fourth: i8 = unsafe { intrinsics::simd::simd_extract(swapped, 0) };
    let fifth: i8 = unsafe { intrinsics::simd::simd_extract(reversed, 0) };
    let sixth: i8 = unsafe { intrinsics::simd::simd_extract(funnel_left, 0) };
    let seventh: i8 = unsafe { intrinsics::simd::simd_extract(funnel_right, 0) };
    let eighth: i8 = unsafe { intrinsics::simd::simd_extract(carryless, 0) };
    unsafe {
        need_nonzero(
            (sum ^ product
                ^ unordered_product
                ^ anded
                ^ ored
                ^ xored
                ^ first
                ^ second
                ^ third
                ^ fourth
                ^ fifth
                ^ sixth
                ^ seventh
                ^ eighth) as u32,
        )
    };
}

#[rapx::verify]
pub fn simd_float_intrinsics() {
    let lanes = F32x4([1.25; 4]);
    let other = F32x4([2.0; 4]);
    let absolute = unsafe { intrinsics::simd::simd_fabs(lanes) };
    let minimum = unsafe { intrinsics::simd::simd_minimum_number_nsz(lanes, other) };
    let maximum = unsafe { intrinsics::simd::simd_maximum_number_nsz(lanes, other) };
    let ceiling = unsafe { intrinsics::simd::simd_ceil(lanes) };
    let floor = unsafe { intrinsics::simd::simd_floor(lanes) };
    let rounded = unsafe { intrinsics::simd::simd_round(lanes) };
    let even = unsafe { intrinsics::simd::simd_round_ties_even(lanes) };
    let truncated = unsafe { intrinsics::simd::simd_trunc(lanes) };
    let root = unsafe { intrinsics::simd::simd_fsqrt(lanes) };
    let fused = unsafe { intrinsics::simd::simd_fma(lanes, other, lanes) };
    let relaxed = unsafe { intrinsics::simd::simd_relaxed_fma(lanes, other, lanes) };
    let sine = unsafe { intrinsics::simd::simd_fsin(lanes) };
    let cosine = unsafe { intrinsics::simd::simd_fcos(lanes) };
    let exponential = unsafe { intrinsics::simd::simd_fexp(lanes) };
    let exponential2 = unsafe { intrinsics::simd::simd_fexp2(lanes) };
    let logarithm10 = unsafe { intrinsics::simd::simd_flog10(lanes) };
    let logarithm2 = unsafe { intrinsics::simd::simd_flog2(lanes) };
    let logarithm = unsafe { intrinsics::simd::simd_flog(lanes) };
    let converted: F32x4 = unsafe { intrinsics::simd::simd_cast(I32x4([1; 4])) };
    let saturating: I32x4 = unsafe { intrinsics::simd::simd_as(lanes) };
    let vectors = [
        absolute,
        minimum,
        maximum,
        ceiling,
        floor,
        rounded,
        even,
        truncated,
        root,
        fused,
        relaxed,
        sine,
        cosine,
        exponential,
        exponential2,
        logarithm10,
        logarithm2,
        logarithm,
    ];
    let mut result = unsafe { intrinsics::simd::simd_extract::<_, f32>(converted, 0) }.to_bits();
    result ^= unsafe { intrinsics::simd::simd_extract::<_, i32>(saturating, 0) } as u32;
    for vector in vectors {
        result ^= unsafe { intrinsics::simd::simd_extract::<_, f32>(vector, 0) }.to_bits();
    }
    unsafe { need_nonzero(result) };
}

#[rapx::verify]
pub fn simd_pointer_intrinsics() {
    use intrinsics::simd::SimdAlign;

    let mut values = [1_i32; 4];
    let ptr = values.as_mut_ptr();
    let pointers = MutPtrx4([ptr; 4]);
    let mask = I32x4([0; 4]);
    let lanes = I32x4([1; 4]);
    let gathered = unsafe { intrinsics::simd::simd_gather(lanes, pointers, mask) };
    unsafe { intrinsics::simd::simd_scatter(lanes, pointers, mask) };
    let loaded = unsafe {
        intrinsics::simd::simd_masked_load::<_, _, _, { SimdAlign::Element }>(mask, ptr, lanes)
    };
    unsafe {
        intrinsics::simd::simd_masked_store::<_, _, _, { SimdAlign::Element }>(mask, ptr, lanes)
    };
    let offset = unsafe { intrinsics::simd::simd_arith_offset(pointers, Isizex4([0; 4])) };
    let const_pointers: Ptrx4 = unsafe { intrinsics::simd::simd_cast_ptr(offset) };
    let addresses: Usizex4 = unsafe { intrinsics::simd::simd_expose_provenance(const_pointers) };
    let reconstructed: Ptrx4 = unsafe { intrinsics::simd::simd_with_exposed_provenance(addresses) };
    let first: i32 = unsafe { intrinsics::simd::simd_extract(gathered, 0) };
    let second: i32 = unsafe { intrinsics::simd::simd_extract(loaded, 0) };
    let recovered: *const i32 = unsafe { intrinsics::simd::simd_extract(reconstructed, 0) };
    unsafe { need_nonzero((first ^ second ^ values[0]) as u32 ^ (recovered == ptr) as u32) };
}

#[rapx::verify]
pub fn simd_add_flow() {
    let one: I8x16 = unsafe { intrinsics::simd::simd_splat(1_i8) };
    let zero: I8x16 = unsafe { intrinsics::simd::simd_splat(0_i8) };
    let result = unsafe { intrinsics::simd::simd_add(one, zero) };
    let first: i8 = unsafe { intrinsics::simd::simd_extract(result, 0) };
    unsafe { need_nonzero(first as u32) };
}

#[rapx::verify]
pub fn simd_insert_flow() {
    let zero: I8x16 = unsafe { intrinsics::simd::simd_splat(0_i8) };
    let inserted = unsafe { intrinsics::simd::simd_insert(zero, 0, 1_i8) };
    let first: i8 = unsafe { intrinsics::simd::simd_extract(inserted, 0) };
    unsafe { need_nonzero(first as u32) };
}

#[rapx::verify]
pub fn simd_extract_bounds_unsound(index: u32) {
    let lanes = I8x16([1; 16]);
    let _: i8 = unsafe { intrinsics::simd::simd_extract_dyn(lanes, index) };
}

#[rapx::verify]
pub fn simd_dyn_insert_flow() {
    let zero: I8x16 = unsafe { intrinsics::simd::simd_splat(0_i8) };
    let inserted = unsafe { intrinsics::simd::simd_insert_dyn(zero, 0, 1_i8) };
    let first: i8 = unsafe { intrinsics::simd::simd_extract_dyn(inserted, 0) };
    unsafe { need_nonzero(first as u32) };
}

#[rapx::verify]
pub fn simd_compare_flow() {
    let one: I8x16 = unsafe { intrinsics::simd::simd_splat(1_i8) };
    let mask: I8x16 = unsafe { intrinsics::simd::simd_eq(one, one) };
    let bits: u16 = unsafe { intrinsics::simd::simd_bitmask(mask) };
    unsafe { need_nonzero(bits as u32) };
}

#[rapx::verify]
pub fn simd_zero_flow_unsound() {
    let zero: I8x16 = unsafe { intrinsics::simd::simd_splat(0_i8) };
    let result = unsafe { intrinsics::simd::simd_add(zero, zero) };
    let first: i8 = unsafe { intrinsics::simd::simd_extract(result, 0) };
    unsafe { need_nonzero(first as u32) };
}

#[rapx::verify]
pub fn simd_gather_zero_mask_flow() {
    let fallback = I32x4([1; 4]);
    let pointers = MutPtrx4([core::ptr::null_mut(); 4]);
    let mask = I32x4([0; 4]);
    let result = unsafe { intrinsics::simd::simd_gather(fallback, pointers, mask) };
    let first: i32 = unsafe { intrinsics::simd::simd_extract(result, 0) };
    unsafe { need_nonzero(first as u32) };
}

#[rapx::verify]
pub fn simd_masked_load_zero_mask_flow() {
    use intrinsics::simd::SimdAlign;

    let value = 0_i32;
    let fallback = I32x4([1; 4]);
    let mask = I32x4([0; 4]);
    let result = unsafe {
        intrinsics::simd::simd_masked_load::<_, _, _, { SimdAlign::Element }>(mask, &value, fallback)
    };
    let first: i32 = unsafe { intrinsics::simd::simd_extract(result, 0) };
    unsafe { need_nonzero(first as u32) };
}

#[rapx::verify]
pub fn simd_scatter_zero_mask_flow() {
    let mut value = 1_i32;
    let pointers = MutPtrx4([&mut value; 4]);
    let mask = I32x4([0; 4]);
    unsafe { intrinsics::simd::simd_scatter(I32x4([0; 4]), pointers, mask) };
    unsafe { need_nonzero(value as u32) };
}

#[rapx::verify]
pub fn simd_masked_store_zero_mask_flow() {
    use intrinsics::simd::SimdAlign;

    let mut value = 1_i32;
    let mask = I32x4([0; 4]);
    unsafe {
        intrinsics::simd::simd_masked_store::<_, _, _, { SimdAlign::Element }>(
            mask,
            &mut value,
            I32x4([0; 4]),
        )
    };
    unsafe { need_nonzero(value as u32) };
}

#[rapx::verify]
pub fn simd_masked_store_active_unsound() {
    use intrinsics::simd::SimdAlign;

    let mut values = [1_i32; 4];
    let mask = I32x4([-1, 0, 0, 0]);
    unsafe {
        intrinsics::simd::simd_masked_store::<_, _, _, { SimdAlign::Element }>(
            mask,
            values.as_mut_ptr(),
            I32x4([0; 4]),
        )
    };
    unsafe { need_nonzero(values[0] as u32) };
}
