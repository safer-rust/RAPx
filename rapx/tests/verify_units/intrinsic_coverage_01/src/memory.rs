use super::need_nonzero;
use core::intrinsics;

#[rapx::verify]
pub fn memory_intrinsics(value: u32) {
    let mut source = value;
    let mut target = 0_u32;
    unsafe { intrinsics::copy_nonoverlapping(&source, &mut target, 1) };
    unsafe { intrinsics::volatile_store(&mut target, source) };
    let loaded = unsafe { intrinsics::volatile_load(&target) };
    unsafe { intrinsics::write_bytes(&mut source, 0, 0) };
    let equal = unsafe { intrinsics::raw_eq(&source, &target) };
    let cmp = unsafe {
        intrinsics::compare_bytes(
            (&source as *const u32).cast(),
            (&target as *const u32).cast(),
            4,
        )
    };
    let ptr = intrinsics::ptr_mask(&source as *const u32, usize::MAX);
    let distance = unsafe { intrinsics::ptr_offset_from(ptr, &source) };
    let shifted = unsafe { intrinsics::arith_offset(ptr, 0) };
    let result = loaded
        ^ target
        ^ (equal as u32)
        ^ (cmp as u32)
        ^ (distance as u32)
        ^ (shifted == ptr) as u32;
    unsafe { need_nonzero(result) };
}

#[rapx::verify]
pub fn more_memory_intrinsics(value: u32) {
    let mut source = value;
    let mut target = 0_u32;
    let mut other = 1_u32;
    let source_ptr = &mut source as *mut u32;
    let target_ptr = &mut target as *mut u32;
    let other_ptr = &mut other as *mut u32;
    unsafe { intrinsics::copy(source_ptr, target_ptr, 1) };
    unsafe { intrinsics::volatile_copy_nonoverlapping_memory(other_ptr, source_ptr, 1) };
    unsafe { intrinsics::volatile_copy_memory(target_ptr, other_ptr, 1) };
    unsafe { intrinsics::unaligned_volatile_store(target_ptr, value) };
    let loaded = unsafe { intrinsics::unaligned_volatile_load(target_ptr) };
    unsafe { intrinsics::nontemporal_store(target_ptr, loaded) };
    unsafe { intrinsics::typed_swap_nonoverlapping(target_ptr, other_ptr) };
    unsafe { intrinsics::volatile_set_memory(source_ptr, 0, 0) };
    let shifted = unsafe { intrinsics::offset(source_ptr, 0_isize) };
    let distance = unsafe { intrinsics::ptr_offset_from_unsigned(shifted, source_ptr) };
    let slice: *const [u32] = &[source, target, other];
    let length: usize = intrinsics::ptr_metadata(slice);
    let rebuilt: *const [u32] = intrinsics::aggregate_raw_ptr(slice as *const u32, length);
    unsafe {
        need_nonzero(
            loaded ^ target ^ other ^ (distance as u32) ^ core::ptr::eq(rebuilt, slice) as u32,
        )
    };
}

#[rapx::verify]
pub fn pointer_misc_intrinsics(value: u32) {
    let pointer = &value as *const u32;
    intrinsics::prefetch_read_data::<u32, 3>(pointer);
    intrinsics::prefetch_write_data::<u32, 3>(pointer);
    intrinsics::prefetch_read_instruction::<u32, 3>(pointer);
    intrinsics::prefetch_write_instruction::<u32, 3>(pointer);
    let slice = &[value];
    let slice_pointer = slice as *const [u32];
    let index = 0_usize;
    let element: *const u32 = unsafe { intrinsics::slice_get_unchecked(slice_pointer, index) };
    let bytes: [u8; 4] = unsafe { intrinsics::transmute(value) };
    let unchanged: u32 = unsafe { intrinsics::transmute_unchecked(value) };
    intrinsics::forget(bytes);
    unsafe { need_nonzero(unchanged ^ (element == pointer) as u32) };
}

#[rapx::verify]
pub fn volatile_store_flow() {
    let mut value = 0_u32;
    unsafe { intrinsics::unaligned_volatile_store(&mut value, 1) };
    let loaded = unsafe { intrinsics::unaligned_volatile_load(&value) };
    unsafe { need_nonzero(loaded) };
}

#[rapx::verify]
pub fn nontemporal_store_flow() {
    let mut value = 0_u32;
    unsafe { intrinsics::nontemporal_store(&mut value, 1) };
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub fn volatile_copy_flow() {
    let source = 1_u32;
    let mut target = 0_u32;
    unsafe { intrinsics::volatile_copy_memory(&mut target, &source, 1) };
    unsafe { need_nonzero(target) };
}

#[rapx::verify]
pub fn volatile_copy_nonoverlapping_flow() {
    let source = 1_u32;
    let mut target = 0_u32;
    unsafe { intrinsics::volatile_copy_nonoverlapping_memory(&mut target, &source, 1) };
    unsafe { need_nonzero(target) };
}

#[rapx::verify]
pub fn volatile_copy_nonoverlapping_overlap_unsound() {
    let mut value = 1_u32;
    let pointer = &mut value as *mut u32;
    unsafe { intrinsics::volatile_copy_nonoverlapping_memory(pointer, pointer, 1) };
}
