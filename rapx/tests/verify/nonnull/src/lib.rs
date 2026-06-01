#![feature(register_tool)]
#![register_tool(rapx)]

// Local unsafe API used to test a direct NonNull obligation.
//
// The verifier reads this source-level contract and creates one required
// property at each callsite:
//
//   NonNull(arg0)
//
// This is intentionally smaller than `ptr::read`, whose std contract expands to
// ValidPtr + Align + Typed.
#[rapx::requires(NonNull(0), kind = "precond")]
unsafe fn require_non_null_arg0(_ptr: *const u32) {}

// Raw pointer input case.
//
// `ptr.add(i).read()` happens inside a loop. The path extractor should produce
// a loop-header path, but the fact checker should not prove NonNull/Align from
// the raw pointer parameter alone. This is a conservative Unknown case.
#[rapx::verify]
pub unsafe fn read_first_nonzero(ptr: *const u32, len: usize) -> u32 {
    let mut i = 0;

    while i < len {
        let current = unsafe { ptr.add(i) };
        let value = unsafe { current.read() };

        if value != 0 {
            return value;
        }

        i += 1;
    }

    0
}

// Slice source case.
//
// This case checks whether the current visitors can follow a pointer produced
// by `slice.as_ptr()` through `ptr.add(i).read()` inside a loop. The path for
// the loop-internal read carries an entry prefix, so the backward visitor should
// retain the pre-loop `as_ptr()` evidence. The fact checker can use that local
// provenance to prove the primitive NonNull/Align pieces, while the full
// ValidPtr obligation still remains Unknown until allocation, bounds,
// initialization, and typing checks are implemented.
#[rapx::verify]
pub fn read_first_nonzero_slice(data: &[u32]) -> u32 {
    let ptr = data.as_ptr();
    let mut i = 0;

    while i < data.len() {
        let current = unsafe { ptr.add(i) };
        let value = unsafe { current.read() };

        if value != 0 {
            return value;
        }

        i += 1;
    }

    0
}

// Stack reference source case.
//
// The pointer read inside the loop comes from `&value as *const u32`. The
// visitors should keep the reference-to-raw-pointer MIR evidence in the loop
// body, allowing the fact checker to prove the Align obligation for
// `ptr::read`. ValidPtr remains Unknown because allocation, bounds,
// initialization, and typing are not fully checked yet.
#[rapx::verify]
pub fn read_stack_ref_loop(limit: usize) -> u32 {
    let value = 7_u32;
    let mut i = 0;

    while i < limit {
        let ptr = &value as *const u32;
        let read_back = unsafe { ptr.read() };

        if read_back != 0 {
            return read_back;
        }

        i += 1;
    }

    0
}

// Direct NonNull checker case.
//
// The local unsafe callee only requires `NonNull(arg0)`. Since the pointer is
// derived from a stack reference in the same loop body, the fact checker should
// prove this obligation without needing SMT or a full ValidPtr proof.
#[rapx::verify]
pub fn call_non_null_loop(limit: usize) {
    let value = 7_u32;
    let mut i = 0;

    while i < limit {
        let ptr = &value as *const u32;
        unsafe {
            require_non_null_arg0(ptr);
        }
        i += 1;
    }
}
