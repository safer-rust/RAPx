//! Unified range test collection (single-file version).
//!
//! Goals:
//! 1. Cover the core requirements from existing testcases under `rapx/tests/range`;
//! 2. Keep all test points in one `lib.rs` for easier review and maintenance;
//! 3. Use comments on each testcase to state exactly what is being tested.

use std::slice;

// ============================================================================
// 1) Pure numeric computation / interval propagation
// ============================================================================

/// testcase: Coupled-variable convergence loop (from range_1)
///
/// Test intent:
/// - Verify joint interval updates for multiple variables (`i`, `j`, `k`) in loops;
/// - Verify that while-conditions and loop-body assignments continuously tighten bounds;
/// - Verify stable convergence behavior under nested loops.
pub fn numeric_coupled_loop() {
    while k < 100 {
        let mut i = 0usize;
        let mut j = k;
        while i < j {
            i += 1;
            j -= 1;
        }
        k += 1;
    }
}

/// testcase: Cross-function argument/return intervals (from range_2)
///
/// Test intent:
/// - Verify argument intervals are propagated from callsite to callee;
/// - Verify return-value intervals are propagated back after callee-side loop updates;
/// - Cover inter-procedural analysis behavior.
pub fn interprocedural_ranges(foo1_seed: usize, foo2_seed: usize, upper_bound: usize) -> usize {
    fn foo1(mut k: usize, upper_bound: usize) {
        while k < upper_bound {
            k += 1;
        }
    }
    fn foo2(mut k: usize, upper_bound: usize) -> usize {
        while k < upper_bound {
            k += 1;
        }
        k
    }

    foo1(foo1_seed, upper_bound);
    foo2(foo2_seed, upper_bound)
}

/// testcase: Branch path constraints (from range_3)
///
/// Test intent:
/// - Verify path-condition constraints in if/else multi-branch control flow;
/// - Verify interval merge behavior at join points after branch-specific updates;
/// - Cover constraint reasoning with nested branches and comparisons.
pub fn path_constraints_branching(x: i32, mut y: i32, z: i32) -> i32 {
    if x < y {
        y += 1;
    } else {
        y -= 1;
        if y > z {
            y -= 2;
        } else {
            y += 2;
        }
    }
    y
}

/// testcase: Recursive path (from range_4)
///
/// Test intent:
/// - Verify monotonic parameter decrease across recursive calls;
/// - Verify path separation between base case (`n <= 0`) and recursive case;
/// - Cover interval stability under self-recursive functions.
pub fn recursion_countdown(n: i32) -> i32 {
    if n <= 0 {
        0
    } else {
        recursion_countdown(n - 1)
    }
}

/// testcase: Symbolic-expression intervals (from range_symbolic)
///
/// Test intent:
/// - Verify modeling of symbolic relations such as `x + 1` and `z - y`;
/// - Verify branch reachability and resulting intervals in an always-true condition (`y > x`);
/// - Cover symbolic interval expressiveness.
pub fn symbolic_interval_case(x: i32) -> i32 {
    let y = x + 1;
    let z = y + 1;
    if y > x {
        z - y
    } else {
        z - x
    }
}

// ============================================================================
// 2) Array/slice length and index ranges
// ============================================================================

/// testcase: for-loop with slice.len() (from range_array)
///
/// Test intent:
/// - Verify inferred slice length from `&mut a[1..slice_index]`;
/// - Verify index safety for `slice[i]` under `for i in 0..slice.len()`;
/// - Cover the common pattern where loop upper-bound is driven by slice length.
pub fn slice_len_for_loop(a: &mut [usize; 10], slice_start: usize, slice_end: usize) {
    if slice_start >= slice_end || slice_end > a.len() {
        return;
    }
    let slice = &mut a[slice_start..slice_end];
    for i in 0..slice.len() {
        slice[i] = i + 1;
    }
}





/// testcase: String/byte indexing and character ranges (from range_5)
///
/// Test intent:
/// - Verify the byte-indexing pattern `string.as_bytes()[0]`;
/// - Verify slicing with `input[..i]` / `input[i+1..]` under `char_indices` and match branches;
/// - Cover realistic character classification plus index slicing flow.
pub fn parse_scheme_case(input: &str, context: bool) -> Option<(String, &str)> {
    #[derive(PartialEq, Eq)]
    enum Context {
        UrlParser,
        Setter,
    }

    #[inline]
    fn starts_with_ascii_alpha(string: &str) -> bool {
        !string.is_empty() && matches!(string.as_bytes()[0], b'a'..=b'z' | b'A'..=b'Z')
    }

    if input.is_empty() || !starts_with_ascii_alpha(input) {
        return None;
    }

    for (i, c) in input.char_indices() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '+' | '-' | '.' => (),
            ':' => return Some((input[..i].to_ascii_lowercase(), &input[i + 1..])),
            _ => return None,
        }
    }

    let mode = if context {
        Context::Setter
    } else {
        Context::UrlParser
    };

    match mode {
        Context::Setter => Some((input.to_ascii_lowercase(), "")),
        Context::UrlParser => None,
    }
}



// ============================================================================
// 3) BCE (Bounds Check Elimination) scenarios LLVM usually cannot eliminate but
//    can be optimized by range analysis 
// ============================================================================



#[inline(never)]
pub fn bce_fail_2d_grid(grid: &[i32], width: usize, height: usize) -> i32 {
    if grid.len() != width * height { return 0; }
    let mut sum = 0;
    for y in 0..height {
        for x in 0..width {
            sum += grid[y * width + x]; // BCE FAILS here in LLVM
        }
    }
    sum
}

// ============================================================================
// 4) BCE scenarios LLVM usually cannot eliminate and range analysis also struggles 
// to eliminate without memory ssa
// ============================================================================

/// testcase: Indirect indexing (BCE failure)
///
/// Test intent:
/// - `idx` is data-dependent from `indices[i]`;
/// - LLVM cannot statically prove `data[idx]` is always in-bounds;
/// - Bounds checks are expected to remain.
///
/// Preconditions:
/// - Every value in `indices` must be a valid index into `data`;
/// - This case focuses on BCE behavior, not panic handling for invalid inputs.
pub fn bce_failure_indirect_indexing(data: &[i32], indices: &[usize]) -> i32 {
    let mut sum = 0;
    for i in 0..indices.len() {
        let idx = indices[i];
        sum += data[idx];
    }
    sum
}

/// testcase: Container-length mutation inside loop (BCE failure)
///
/// Test intent:
/// - `push` inside the loop may change vector length;
/// - The compiler cannot reliably reuse prior bounds proofs;
/// - `v[i]` checks are expected to be hard to fully eliminate.
pub fn bce_failure_mutation_invalidation(v: &mut Vec<i32>) {
    let len = v.len();
    for i in 0..len {
        let val = v[i];
        v.push(val * 2);
    }
}

/// testcase: Complex-step induction variable (BCE failure)
///
/// Test intent:
/// - Dynamic stride in `step_by(dynamic_step)` complicates induction proofs;
/// - The compiler often cannot prove every access is in-bounds;
/// - `slice[i]` checks are expected to remain in many cases.
pub fn bce_failure_complex_induction(slice: &[i32], dynamic_step: usize) -> i32 {
    if dynamic_step == 0 {
        return 0;
    }
    let mut sum = 0;
    for i in (0..slice.len()).step_by(dynamic_step) {
        sum += slice[i];
    }
    sum
}