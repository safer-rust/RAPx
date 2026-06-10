#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[derive(Clone, Copy)]
pub enum Selector {
    First,
    Second,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

fn byte_add_as_u32(base: *const u8, offset: usize) -> *const u32 {
    unsafe { base.add(offset) as *const u32 }
}

fn choose_byte_ptr(base: *const u8, offset: usize, choice: Selector) -> *const u32 {
    match choice {
        Selector::First => unsafe { base.add(offset) as *const u32 },
        Selector::Second => base as *const u32,
    }
}

fn maybe_unaligned(base: *const u8, choice: Selector) -> *const u32 {
    match choice {
        Selector::First => base as *const u32,
        Selector::Second => unsafe { base.add(1) as *const u32 },
    }
}

fn hop2(base: *const u8, offset: usize) -> *const u32 {
    byte_add_as_u32(base, offset)
}

fn hop1(base: *const u8, offset: usize) -> *const u32 {
    hop2(base, offset)
}

// SOUND: helper result is guarded by both base and offset alignment checks.
// This stresses call-summary transfer before the unsafe API.
#[rapx::verify]
pub fn sound_helper_with_conjunctive_guard(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && offset % 4 == 0 {
        let ptr = byte_add_as_u32(base, offset);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

// UNSOUND: `||` does not imply both base and offset are aligned.
// The verifier must not treat either side as a must fact.
#[rapx::verify]
pub fn unsound_helper_with_disjunctive_guard(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 || offset % 4 == 0 {
        let ptr = byte_add_as_u32(base, offset);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

// SOUND: nested path conditions jointly prove the helper result is aligned.
// The relevant branch facts are split across two basic blocks.
#[rapx::verify]
pub fn sound_nested_if_before_helper(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        if offset % 4 == 0 {
            let ptr = byte_add_as_u32(base, offset);
            unsafe {
                require_align_arg0(ptr);
            }
        }
    }
}

// UNSOUND: one helper return path can select `base + 1`.
// The enum branch controls the returned pointer before the unsafe API.
#[rapx::verify]
pub fn unsound_helper_return_path_selects_bad_ptr(data: &[u8], choice: Selector) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        let ptr = maybe_unaligned(base, choice);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

// SOUND: both helper return alternatives are aligned under the caller guard.
// This checks path-sensitive summary merge across a small match.
#[rapx::verify]
pub fn sound_helper_return_paths_all_aligned(data: &[u8], offset: usize, choice: Selector) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && offset % 4 == 0 {
        let ptr = choose_byte_ptr(base, offset, choice);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

// SOUND: multi-hop helpers preserve the guarded pointer arithmetic relation.
// This prevents summaries from stopping at the first intra-crate call.
#[rapx::verify]
pub fn sound_multi_hop_helper(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 && offset % 4 == 0 {
        let ptr = hop1(base, offset);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

// UNSOUND: the multi-hop helper still needs the offset-alignment guard.
// A base-address guard alone is not enough after byte arithmetic.
#[rapx::verify]
pub fn unsound_multi_hop_missing_offset_guard(data: &[u8], offset: usize) {
    let base = data.as_ptr();

    if (base as usize) % 4 == 0 {
        let ptr = hop1(base, offset);
        unsafe {
            require_align_arg0(ptr);
        }
    }
}

// SOUND: unrelated path conditions must not pollute the align proof.
// Only the base/offset guards should matter for the unsafe argument.
#[rapx::verify]
pub fn sound_unrelated_condition_ignored(data: &[u8], offset: usize, noise: usize) {
    let base = data.as_ptr();

    if noise % 3 == 1 {
        if (base as usize) % 4 == 0 && offset % 4 == 0 {
            let ptr = byte_add_as_u32(base, offset);
            unsafe {
                require_align_arg0(ptr);
            }
        }
    }
}
