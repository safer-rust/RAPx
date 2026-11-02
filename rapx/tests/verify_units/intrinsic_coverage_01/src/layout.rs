use super::need_nonzero;
use core::intrinsics;

#[rapx::verify]
pub fn layout_intrinsics(value: u32) {
    let a = const { intrinsics::size_of::<u32>() } as u32;
    let b = const { intrinsics::align_of::<u32>() } as u32;
    let c = unsafe { intrinsics::size_of_val(&value) } as u32;
    let d = unsafe { intrinsics::align_of_val(&value) } as u32;
    let e = const { intrinsics::needs_drop::<u32>() } as u32;
    let f = const { intrinsics::type_name::<u32>() }.len() as u32;
    let g = const { intrinsics::offset_of::<(u8, u32)>(0, 1) } as u32;
    let h = const { intrinsics::variant_count::<Option<u32>>() } as u32;
    #[cfg(rapx_ge_100)]
    let i = intrinsics::reflection::type_id_eq(
        const { intrinsics::reflection::type_id::<u32>() },
        const { intrinsics::reflection::type_id::<u64>() },
    ) as u32;
    #[cfg(not(rapx_ge_100))]
    let i = 0_u32;
    unsafe { need_nonzero(a ^ b ^ c ^ d ^ e ^ f ^ g ^ h ^ i ^ value) };
}

#[rapx::verify]
pub fn layout_reflection_intrinsics(value: u32) {
    intrinsics::assert_inhabited::<u32>();
    intrinsics::assert_zero_valid::<u32>();
    intrinsics::assert_mem_uninitialized_valid::<core::mem::MaybeUninit<u32>>();
    intrinsics::cold_path();
    let location = intrinsics::caller_location();
    let variant = intrinsics::discriminant_value(&Some(value));
    let pointer = &value as *const u32;
    let comparison = intrinsics::ptr_guaranteed_cmp(pointer, pointer);
    let result = location.line() ^ location.column() ^ (comparison as u32) ^ value;
    core::hint::black_box(variant);
    unsafe { need_nonzero(result) };
}
