#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

use core::mem::MaybeUninit;

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_u32(_ptr: *const u32) {}

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull_u32(_ptr: *const u32) {}

#[rapx::requires(InBound(_ptr, u32, 1), kind = "precond")]
unsafe fn require_inbound_u32(_ptr: *const u32) {}

#[rapx::requires(Allocated(_ptr, u32, 1), kind = "precond")]
unsafe fn require_allocated_u32(_ptr: *const u32) {}

#[rapx::requires(ValidPtr(_ptr, u32, 1), kind = "precond")]
unsafe fn require_validptr_u32(_ptr: *const u32) {}

#[rapx::requires(Deref(_ptr, u32, 1), kind = "precond")]
unsafe fn require_deref_u32(_ptr: *const u32) {}

#[rapx::requires(Init(_ptr, u32, 1), kind = "precond")]
unsafe fn require_init_u32(_ptr: *const u32) {}

#[rapx::requires(Typed(_ptr, u32), kind = "precond")]
unsafe fn require_typed_u32(_ptr: *const u32) {}

#[rapx::requires(ValidNum(_value < 4), kind = "precond")]
unsafe fn require_less_than_four(_value: usize) {}

#[rapx::requires(ValidNum(_value % 2 == 1), kind = "precond")]
unsafe fn require_odd_usize(_value: usize) {}

// THRESHOLD: repeat=1 can exit after at most three loop bodies and checks the
// aligned pointer; repeat=2 can reach the delayed unaligned overwrite.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_align(good_ref: &u32, limit: usize) {
    let good = good_ref as *const u32 as *const u8;
    let bad = good.wrapping_add(1);
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_align_u32(selected as *const u32);
    }
}

// THRESHOLD: repeat=1 can exit after at most three loop bodies and keeps the
// reference-derived pointer intact; repeat=2 reaches the delayed null source.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_nonnull(good_ref: &u32, limit: usize) {
    let good = good_ref as *const u32;
    let bad = core::ptr::null::<u32>();
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_nonnull_u32(selected);
    }
}

// THRESHOLD: repeat=1 can exit after at most three loop bodies and keeps the
// live allocation source; repeat=2 reaches the delayed null allocation.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_allocated(good_ref: &u32, limit: usize) {
    let good = good_ref as *const u32;
    let bad = core::ptr::null::<u32>();
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_allocated_u32(selected);
    }
}

// THRESHOLD: ValidPtr is a compound pointer-validity check; the null pointer
// only reaches the final call at repeat=2.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_validptr(good_ref: &u32, limit: usize) {
    let good = good_ref as *const u32;
    let bad = core::ptr::null::<u32>();
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_validptr_u32(selected);
    }
}

// THRESHOLD: Deref reduces to allocation plus bounds, both depending on the
// delayed loop-carried pointer state.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_deref(good_ref: &u32, limit: usize) {
    let good = good_ref as *const u32;
    let bad = core::ptr::null::<u32>();
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_deref_u32(selected);
    }
}

// THRESHOLD: repeat=1 sees only the initialized reference-derived source;
// repeat=2 can expose the uninitialized MaybeUninit slot.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_init(good_ref: &u32, limit: usize) {
    let slot = MaybeUninit::<u32>::uninit();
    let good = good_ref as *const u32;
    let bad = slot.as_ptr();
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_init_u32(selected);
    }
}

// THRESHOLD: Typed follows provenance through no-op pointer transfers; repeat=2
// is needed before the untyped byte source reaches `selected`.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_typed(
    good_ref: &u32,
    bytes: &[u8; 4],
    limit: usize,
) {
    let good = good_ref as *const u32;
    let bad = bytes.as_ptr() as *const u32;
    let mut selected = good;
    let mut current = good;
    let mut next = good;
    let mut after_next = good;
    let mut i = 0usize;

    while i < limit {
        selected = current.wrapping_add(0);
        current = next.wrapping_add(0);
        next = after_next.wrapping_add(0);
        after_next = bad;
        i += 1;
    }

    unsafe {
        require_typed_u32(selected);
    }
}

// THRESHOLD: this is an index/dataflow case.
// repeat=1 reaches offsets 1, 2, and 3 under len >= 4; repeat=2 can
// reach offset 4, which is not valid for one element.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_inbound_counter(data: &[u32]) {
    let len = data.len();
    if len < 4 {
        return;
    }

    let ptr = data.as_ptr();
    let mut i = 0usize;

    while i < len {
        let current = ptr.wrapping_add(i + 1);
        unsafe {
            require_inbound_u32(current);
        }
        i += 1;
    }
}

// THRESHOLD: the loop-carried numeric state stays below the contract threshold
// in shallow prefixes, but reaches 4 at the next unrolling depth.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_validnum_counter(limit: usize) {
    let mut value = 0usize;
    let mut i = 0usize;

    while i < limit {
        value += 1;
        i += 1;
    }

    unsafe {
        require_less_than_four(value);
    }
}

// THRESHOLD: the numeric state is periodic, not monotonic.  The bad even value
// oscillates through a delayed loop-carried chain, so a planner that commits to
// one exact witness depth can miss the parity that violates `value % 2 == 1`.
#[rapx::verify]
pub fn repeat1_sound_repeat2_unsound_validnum_parity_oscillation(limit: usize) {
    let mut selected = 1usize;
    let mut current = 1usize;
    let mut next = 1usize;
    let mut after_next = 1usize;
    let mut i = 0usize;

    while i < limit {
        selected = current;
        current = next;
        next = after_next;
        after_next = 1usize - after_next;
        i += 1;
    }

    unsafe {
        require_odd_usize(selected);
    }
}
