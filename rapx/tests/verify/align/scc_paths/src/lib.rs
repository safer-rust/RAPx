#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[derive(Clone, Copy)]
pub enum Selector {
    First,
    Second,
}

#[rapx::requires(Align(_ptr, u32), kind = "precond")]
unsafe fn require_align_arg0(_ptr: *const u32) {}

// SOUND: named contract parameter `_ptr` must bind to this callsite argument.
#[rapx::verify]
pub fn sound_named_contract_binds_callsite_arg(data: &[u32]) {
    let ptr = data.as_ptr();

    unsafe {
        require_align_arg0(ptr);
    }
}

// SOUND: both SCC paths produce a u32-aligned pointer before the unsafe API.
#[rapx::verify]
pub fn sound_enum_paths_inside_scc(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => base,
            Selector::Second => unsafe { base.add(i) },
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected);
    }
}

// UNSOUND: one SCC path leaves `selected` at `base + 1` byte.
#[rapx::verify]
pub fn unsound_enum_paths_inside_scc(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => unsafe { base.add(i * 4) },
            Selector::Second => unsafe { base.add(i * 4 + 1) },
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// SOUND: SCC source selection changes provenance, but both alternatives align.
#[rapx::verify]
pub fn sound_scc_selects_aligned_source(data: &[u32], limit: usize, choice: Selector) {
    let local = 7_u32;
    let slice_base = data.as_ptr();
    let stack_ptr = &local as *const u32;
    let mut selected = slice_base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => unsafe { slice_base.add(i) },
            Selector::Second => stack_ptr,
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected);
    }
}

// UNSOUND: one source category is a byte-shifted slice pointer.
#[rapx::verify]
pub fn unsound_scc_selects_mixed_source(data: &[u32], limit: usize, choice: Selector) {
    let local = 11_u32;
    let stack_ptr = &local as *const u32 as *const u8;
    let slice_base = data.as_ptr() as *const u8;
    let mut selected = slice_base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => {
                if i % 2 == 0 {
                    slice_base
                } else {
                    stack_ptr
                }
            }
            Selector::Second => unsafe { slice_base.add(1) },
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// SOUND: the SCC computes only offsets divisible by four.
#[rapx::verify]
pub fn sound_scc_computes_aligned_offset(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut byte_offset = 0usize;
    let mut i = 0;

    while i < limit {
        byte_offset = match choice {
            Selector::First => 0,
            Selector::Second => i * 4,
        };

        i += 1;
    }

    let selected = unsafe { base.add(byte_offset) };

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// UNSOUND: the SCC may compute a final byte offset not divisible by four.
#[rapx::verify]
pub fn unsound_scc_computes_misaligned_offset(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut byte_offset = 0usize;
    let mut i = 0;

    while i < limit {
        byte_offset = match choice {
            Selector::First => i * 4,
            Selector::Second => i * 4 + 1,
        };

        i += 1;
    }

    let selected = unsafe { base.add(byte_offset) };

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// SOUND: nested SCCs update the selected pointer only through u32 element moves.
#[rapx::verify]
pub fn sound_nested_scc_controller(
    data: &[u32],
    outer_limit: usize,
    inner_limit: usize,
    choice: Selector,
) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut outer = 0;

    while outer < outer_limit {
        let mut p = match choice {
            Selector::First => base,
            Selector::Second => unsafe { base.add(outer) },
        };

        let q = unsafe { base.add(outer + 1) };
        let mut inner = 0;

        while inner < inner_limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => p,
            };

            p = q;
            inner += 1;
        }

        outer += 1;
    }

    unsafe {
        require_align_arg0(selected);
    }
}

// UNSOUND: after two inner iterations, `p = q` can move `selected` to `base + 1`.
#[rapx::verify]
pub fn unsound_nested_scc_controller(
    data: &[u32],
    outer_limit: usize,
    inner_limit: usize,
    choice: Selector,
) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut outer = 0;

    while outer < outer_limit {
        let mut p = base;
        let q = unsafe { base.add(1) };
        let mut inner = 0;

        while inner < inner_limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => p,
            };

            p = q;
            inner += 1;
        }

        outer += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// SOUND: final value alternates by iteration count, but both offsets align.
#[rapx::verify]
pub fn sound_iteration_count_switches_aligned_offsets(data: &[u32], limit: usize) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = if i % 2 == 0 {
            base
        } else {
            unsafe { base.add(4) }
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// UNSOUND: odd final iteration count can leave `selected` at `base + 1`.
#[rapx::verify]
pub fn unsound_iteration_count_can_leave_unaligned(data: &[u32], limit: usize) {
    let base = data.as_ptr() as *const u8;
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = if i % 2 == 0 {
            base
        } else {
            unsafe { base.add(1) }
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}

// SOUND: the SCC mutates only scratch state unrelated to the unsafe argument.
#[rapx::verify]
pub fn sound_unrelated_scc_does_not_pollute_align(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr() as *const u8;
    let mut scratch = base;
    let mut i = 0;

    while i < limit {
        scratch = match choice {
            Selector::First => unsafe { base.add(i * 4) },
            Selector::Second => unsafe { base.add(i * 4 + 1) },
        };

        i += 1;
    }

    let _ignore = scratch;
    let selected = data.as_ptr();

    unsafe {
        require_align_arg0(selected);
    }
}

// SOUND: nested SCC scratch state is unrelated to the stack pointer argument.
#[rapx::verify]
pub fn sound_unrelated_nested_scc_with_bad_scratch(
    outer_limit: usize,
    inner_limit: usize,
    choice: Selector,
) {
    let value = 19_u32;
    let base = &value as *const u32 as *const u8;
    let mut scratch = base;
    let mut outer = 0;

    while outer < outer_limit {
        let mut inner = 0;

        while inner < inner_limit {
            scratch = match choice {
                Selector::First => base,
                Selector::Second => unsafe { base.add(1) },
            };

            inner += 1;
        }

        outer += 1;
    }

    let _ignore = scratch;
    let selected = &value as *const u32;

    unsafe {
        require_align_arg0(selected);
    }
}

// SOUND: pre-SCC guards and SCC-selected offsets jointly align the final pointer.
// The unsafe API is outside the SCC, after several related path choices.
#[rapx::verify]
pub fn sound_pre_scc_guard_with_scc_offsets(data: &[u8], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    if (base as usize) % 4 == 0 {
        while i < limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => unsafe { base.add(i * 4) },
            };

            i += 1;
        }

        unsafe {
            require_align_arg0(selected as *const u32);
        }
    }
}

// UNSOUND: a related SCC path can overwrite the guarded pointer with `base + 1`.
// The pre-SCC base guard must not prove the post-SCC selected pointer.
#[rapx::verify]
pub fn unsound_pre_scc_guard_overwritten_by_scc(data: &[u8], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    if (base as usize) % 4 == 0 {
        while i < limit {
            selected = match choice {
                Selector::First => base,
                Selector::Second => unsafe { base.add(1) },
            };

            i += 1;
        }

        unsafe {
            require_align_arg0(selected as *const u32);
        }
    }
}

// SOUND: SCC-local branch noise is unrelated to the pointer used after the SCC.
// The final unsafe argument is rebuilt from the aligned slice base.
#[rapx::verify]
pub fn sound_scc_internal_noise_ignored(data: &[u32], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut scratch = base as *const u8;
    let mut i = 0;

    while i < limit {
        if i % 2 == 0 {
            scratch = match choice {
                Selector::First => base as *const u8,
                Selector::Second => unsafe { (base as *const u8).add(1) },
            };
        }

        i += 1;
    }

    let _ignore = scratch;
    let selected = data.as_ptr();

    unsafe {
        require_align_arg0(selected);
    }
}

// UNSOUND: an SCC-internal guard only protects one branch of the selected value.
// Another enum path still assigns an unaligned byte-shifted pointer.
#[rapx::verify]
pub fn unsound_scc_guard_only_on_one_branch(data: &[u8], limit: usize, choice: Selector) {
    let base = data.as_ptr();
    let mut selected = base;
    let mut i = 0;

    while i < limit {
        selected = match choice {
            Selector::First => {
                if (base as usize) % 4 == 0 {
                    base
                } else {
                    unsafe { base.add(4) }
                }
            }
            Selector::Second => unsafe { base.add(1) },
        };

        i += 1;
    }

    unsafe {
        require_align_arg0(selected as *const u32);
    }
}
