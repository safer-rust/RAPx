use super::need_nonzero;
use core::intrinsics;

#[cfg(rapx_ge_100)]
macro_rules! atomic_load_seqcst {
    ($pointer:expr) => {
        intrinsics::atomic_load::<u32, { intrinsics::AtomicOrdering::SeqCst }, false>($pointer)
    };
}

#[cfg(not(rapx_ge_100))]
macro_rules! atomic_load_seqcst {
    ($pointer:expr) => {
        intrinsics::atomic_load::<u32, { intrinsics::AtomicOrdering::SeqCst }>($pointer)
    };
}

#[cfg(rapx_ge_100)]
macro_rules! atomic_store_seqcst {
    ($pointer:expr, $value:expr) => {
        intrinsics::atomic_store::<u32, { intrinsics::AtomicOrdering::SeqCst }, false>(
            $pointer, $value,
        )
    };
}

#[cfg(not(rapx_ge_100))]
macro_rules! atomic_store_seqcst {
    ($pointer:expr, $value:expr) => {
        intrinsics::atomic_store::<u32, { intrinsics::AtomicOrdering::SeqCst }>(
            $pointer, $value,
        )
    };
}

#[rapx::verify]
pub fn atomic_intrinsics(value: u32) {
    use intrinsics::AtomicOrdering::SeqCst;

    let mut cell = value;
    let ptr = &mut cell as *mut u32;
    let loaded = unsafe { atomic_load_seqcst!(ptr) };
    unsafe { atomic_store_seqcst!(ptr, loaded) };
    let old = unsafe { intrinsics::atomic_xchg::<u32, { SeqCst }>(ptr, value) };
    let added = unsafe { intrinsics::atomic_xadd::<u32, u32, { SeqCst }>(ptr, 1) };
    let subtracted = unsafe { intrinsics::atomic_xsub::<u32, u32, { SeqCst }>(ptr, 1) };
    let anded = unsafe { intrinsics::atomic_and::<u32, u32, { SeqCst }>(ptr, value) };
    let ored = unsafe { intrinsics::atomic_or::<u32, u32, { SeqCst }>(ptr, value) };
    let xored = unsafe { intrinsics::atomic_xor::<u32, u32, { SeqCst }>(ptr, value) };
    let nanded = unsafe { intrinsics::atomic_nand::<u32, u32, { SeqCst }>(ptr, value) };
    let mut signed_cell = value as i32;
    let signed_ptr = &mut signed_cell as *mut i32;
    let maximum = unsafe { intrinsics::atomic_max::<i32, { SeqCst }>(signed_ptr, value as i32) };
    let minimum = unsafe { intrinsics::atomic_min::<i32, { SeqCst }>(signed_ptr, value as i32) };
    let unsigned_maximum = unsafe { intrinsics::atomic_umax::<u32, { SeqCst }>(ptr, value) };
    let unsigned_minimum = unsafe { intrinsics::atomic_umin::<u32, { SeqCst }>(ptr, value) };
    let (exchanged, success) =
        unsafe { intrinsics::atomic_cxchg::<u32, { SeqCst }, { SeqCst }>(ptr, value, old) };
    let (weakly_exchanged, weak_success) =
        unsafe { intrinsics::atomic_cxchgweak::<u32, { SeqCst }, { SeqCst }>(ptr, value, old) };
    unsafe { intrinsics::atomic_fence::<{ SeqCst }>() };
    unsafe { intrinsics::atomic_singlethreadfence::<{ SeqCst }>() };
    unsafe {
        need_nonzero(
            loaded
                ^ old
                ^ added
                ^ subtracted
                ^ anded
                ^ ored
                ^ xored
                ^ nanded
                ^ (maximum as u32)
                ^ (minimum as u32)
                ^ unsigned_maximum
                ^ unsigned_minimum
                ^ exchanged
                ^ weakly_exchanged
                ^ (success as u32)
                ^ (weak_success as u32)
                ^ cell,
        )
    };
}

#[rapx::verify]
pub fn atomic_store_load_flow() {
    let mut value = 0_u32;
    let pointer = &mut value as *mut u32;
    unsafe { atomic_store_seqcst!(pointer, 1) };
    let loaded = unsafe { atomic_load_seqcst!(pointer) };
    unsafe { need_nonzero(loaded) };
}

#[rapx::verify]
pub fn atomic_store_load_zero_unsound() {
    let mut value = 1_u32;
    let pointer = &mut value as *mut u32;
    unsafe { atomic_store_seqcst!(pointer, 0) };
    let loaded = unsafe { atomic_load_seqcst!(pointer) };
    unsafe { need_nonzero(loaded) };
}
