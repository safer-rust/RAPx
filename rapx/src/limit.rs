//! Central home for every numeric limit / bound used across the analysis and
//! verification pipeline.
//!
//! Before this module, each limit lived as a module-local `const`/`static` next
//! to its consumer, so thresholds were duplicated (the `16`-block inline cap
//! appeared in both the path graph and the runtime inliner) and hard to audit.
//! Keeping them all here mirrors [`crate::def_id`]: one flat, well-documented
//! location where a knob can be found and tuned without grepping the crate.
//!
//! Everything is `pub(crate)`; names that would otherwise collide across
//! modules (the two `VISIT_LIMIT`s, the two `MAX_DEPTH`s) are prefixed with
//! their owning analysis.

// ─────────────────────────────────────────────────────────────────────────────
// Path enumeration
// ─────────────────────────────────────────────────────────────────────────────

use std::sync::atomic::{AtomicUsize, Ordering};

/// Maximum number of paths collected per search — both whole-CFG enumeration
/// and per-checkpoint prefix collection. Overridable via the `--path-limit`
/// CLI flag.
pub(crate) const PATH_LIMIT: usize = 512;

/// Runtime override for [`PATH_LIMIT`], set from `--path-limit`. `0` means
/// "not overridden" (the default above applies).
static PATH_LIMIT_OVERRIDE: AtomicUsize = AtomicUsize::new(0);

/// Set the `--path-limit` override; `0` restores [`PATH_LIMIT`].
pub(crate) fn set_path_limit(n: usize) {
    PATH_LIMIT_OVERRIDE.store(n, Ordering::Relaxed);
}

/// The effective path cap (override, or [`PATH_LIMIT`]).
pub(crate) fn path_limit() -> usize {
    match PATH_LIMIT_OVERRIDE.load(Ordering::Relaxed) {
        0 => PATH_LIMIT,
        n => n,
    }
}

/// Maximum DFS depth for whole-CFG path enumeration.
pub(crate) const WHOLE_CFG_PATH_DEPTH_LIMIT: usize = 256;

/// Bounded cache size for SCC path enumeration.
pub(crate) const SCC_PATH_CACHE_LIMIT: usize = 2048;

/// Maximum DFS depth for intra-SCC path enumeration.
pub(crate) const SCC_MAX_DEPTH: usize = 128;

/// Maximum number of distinct paths collected per SCC.
pub(crate) const SCC_MAX_SEEN_PATHS: usize = 128;

/// Maximum path length within an SCC traversal.
pub(crate) const SCC_MAX_PATH_LEN: usize = 200;

// ─────────────────────────────────────────────────────────────────────────────
// Inlining
// ─────────────────────────────────────────────────────────────────────────────

/// A local callee is inlined into the path CFG only when its MIR is at most
/// this many basic blocks. This is a *transitive* shape bound: local inlining
/// recurses into the callee's own calls, so every inlined body multiplies the
/// path-graph size. Cross-crate callees are exempt — they are inlined a single
/// level and never recursed into, so their size is not bounded here.
pub(crate) const LOCAL_INLINE_BLOCK_LIMIT: usize = 32;

/// Recursion depth bound for runtime inlining
/// ([`crate::verify::vm::call::exec_inline_call`]). Recursive inlining unwinds
/// through the Rust call stack, so this caps nesting.
pub(crate) const MAX_INLINE_DEPTH: usize = 5;

// ─────────────────────────────────────────────────────────────────────────────
// Loop sensitivity / postfix repeat
// ─────────────────────────────────────────────────────────────────────────────

/// Caps how many times a loop body is unrolled during path enumeration;
/// loop-heavy functions (e.g. UTF-16 decoders) scale super-linearly with it.
/// Lower it to speed up verification at the cost of loop sensitivity (bugs that
/// only manifest after more iterations can be missed).
pub(crate) const MAX_AUTO_REPEAT: usize = 8;

/// Fallback loop-carried distance used when a sink is loop-sensitive but the
/// local transfer graph is too imprecise to calculate a better distance.
///
/// Three backedges calibrates to `allow_repeat = 2`, which is the first depth
/// needed by the delayed pointer/state cases in `loop_repeat_threshold`.
pub(crate) const DEFAULT_LOOP_CARRIED_BACKEDGES: usize = 3;

/// Conservative first numeric witness when an index obligation is known to be
/// induction-sensitive but the current summary cannot yet recover a concrete
/// symbolic bound.
pub(crate) const DEFAULT_NUMERIC_WITNESS_ITERATION: usize = 4;

/// The first repeat depth that reliably exposes the existing delayed
/// loop-carried pointer/state fixtures.
pub(crate) const MIN_DATAFLOW_REPEAT: usize = 2;

// ─────────────────────────────────────────────────────────────────────────────
// Points-to / alias
// ─────────────────────────────────────────────────────────────────────────────

/// Hard cap on the number of values a single points-to path may materialize.
pub(crate) const MAX_VALUES_PER_PATH: usize = 1000;

/// Recursion cap on nested field projection while building a points-to graph.
pub(crate) const MAX_FIELD_DEPTH: usize = 5;

/// Recursion cap on nested dereferences while building a points-to graph.
pub(crate) const MAX_DEREF_DEPTH: usize = 3;

/// Visit cap for the alias-graph DFS/iteration in the default alias analysis.
pub(crate) const ALIAS_VISIT_LIMIT: usize = 80;

// ─────────────────────────────────────────────────────────────────────────────
// SafeDrop
// ─────────────────────────────────────────────────────────────────────────────

/// Visit cap for the SafeDrop graph DFS.
pub(crate) const SAFEDROP_VISIT_LIMIT: usize = 1000;

// ─────────────────────────────────────────────────────────────────────────────
// Call-summary recognition (interprocedural)
// ─────────────────────────────────────────────────────────────────────────────

/// Max basic-block count for a local callee to be recognized as a
/// pointer-arithmetic (add/sub) wrapper summary.
pub(crate) const POINTER_ARITH_WRAPPER_BLOCK_LIMIT: usize = 16;

/// Max basic-block count for a local callee to be recognized as a
/// `from_raw_parts` wrapper summary.
pub(crate) const FROM_RAW_PARTS_WRAPPER_BLOCK_LIMIT: usize = 8;

// ─────────────────────────────────────────────────────────────────────────────
// API dependency
// ─────────────────────────────────────────────────────────────────────────────

/// Upper bound on type complexity accepted when resolving API-dependency
/// output types.
pub(crate) const MAX_TY_COMPLX: usize = 5;

/// Cap on the number of monomorphization steps retained per API-dependency
/// resolution.
pub(crate) const MAX_STEP_SET_SIZE: usize = 1000;

/// Recursion depth cap for the fuzzable-type predicate.
pub(crate) const FUZZABLE_MAX_DEPTH: usize = 64;
