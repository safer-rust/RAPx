//! Interprocedural call summaries for the staged verifier.
//!
//! The backward visitor needs dependency information: when a call result is
//! relevant, which call arguments should become relevant too?  The forward
//! visitor needs effect information: after a retained call, what facts about the
//! return value or arguments can be added or forgotten?
//!
//! This module keeps those summaries in one place.  Standard unsafe/std APIs
//! are summarized by name.  Local callees can additionally use the existing
//! dataflow graph to approximate which arguments flow into the return value.
pub(crate) mod builtin_models;
pub(crate) mod interprocedural;

#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), not(rapx_ge_100)))]
use rustc_hir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), rapx_ge_100))]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Operand},
    ty::{Ty, TyCtxt, TyKind},
};

use crate::compat::FxHashMap;
use crate::helpers::mir_utils;
use crate::verify::api_classify::{is_branch, is_std_vec};

/// Caller constraints that affect a callee's path feasibility, propagated down
/// the call chain during must-write summarization. Only concrete literal
/// arguments are carried for now; symbolic path conditions come later.
#[derive(Clone, Debug, Default)]
pub(crate) struct CallContext {
    /// Concrete literal argument values, keyed by 0-based argument index
    /// (matching `trace_to_callee_arg`).
    pub concrete: FxHashMap<usize, i128>,
}

/// Dependency summary consumed by the backward visitor.
#[derive(Clone, Debug)]
pub(crate) struct CallDependencySummary {
    /// If the call destination is relevant, these call arguments are relevant.
    pub return_depends_on_args: Vec<usize>,
    /// Arguments definitely written on every return path (the must-write
    /// intersection, from `local_must_write_args`). The backward slicer keeps
    /// these relevant so the write effect is applied. A conditionally-written
    /// argument is *not* listed here — that is the "may-write" set, which this
    /// summary does not compute.
    pub must_write_args: Vec<usize>,
    /// True when this summary is conservative rather than precise.
    pub unsupported: bool,
}

impl CallDependencySummary {
    /// Build a conservative summary that keeps all arguments relevant.
    fn unknown(arg_count: usize) -> Self {
        Self {
            return_depends_on_args: (0..arg_count).collect(),
            must_write_args: Vec::new(),
            unsupported: true,
        }
    }
}

/// Effect summary consumed by the forward visitor.
#[derive(Clone, Debug)]
pub(crate) struct CallEffectSummary {
    /// Effects that can be applied to the path-local abstract state.
    pub effects: Vec<CallEffect>,
    /// True when this summary is conservative rather than precise.
    pub unsupported: bool,
}

impl CallEffectSummary {
    /// Build a conservative summary for an unsupported call.
    fn unknown() -> Self {
        Self {
            effects: Vec::new(),
            unsupported: true,
        }
    }
}

/// Path-local effect produced by a retained call.
#[derive(Clone, Debug)]
pub(crate) enum CallEffect {
    /// The return value aliases or is a direct value flow from an argument.
    ReturnAliasArg { arg: usize },
    /// `select_unpredictable(cond, x, y)` returns either `x` or `y`: the result
    /// is one of the two candidate values (`args[1]`/`args[2]`), non-deterministic
    /// since the boolean selector (`args[0]`) is unpredictable.
    SelectUnpredictable,
    /// The return value is a pointer extracted from an aggregate/reference arg.
    ReturnPointerFromArg { arg: usize },
    /// The return value is `base + offset * stride`.
    ReturnPointerAdd {
        base_arg: usize,
        offset_arg: usize,
        stride: Option<u64>,
        /// Whether the result is a *dereferenceable* pointer (its contract
        /// guarantees strict in-bounds, e.g. `SliceIndex::get_unchecked`), as
        /// opposed to plain `add` arithmetic whose result may be one-past-end.
        dereferenceable: bool,
    },
    /// The return value is `base - offset * stride`.
    ReturnPointerSub {
        base_arg: usize,
        offset_arg: usize,
        stride: Option<u64>,
    },
    /// The return value is known to be non-zero.
    ReturnNonZero,
    /// The return value is known to satisfy a concrete alignment.
    ReturnAligned,
    /// The return value is a concrete layout/numeric constant.
    ReturnConst { value: u64 },
    /// The call writes one initialized element through a pointer argument.
    WriteMemory { pointer_arg: usize },
    /// The return value is a pointer backed by a fresh allocation of
    /// `size_arg` elements × `elem_size` bytes. The base address is taken
    /// from `pointer_arg`. Used for `from_raw_parts(ptr, len)`.
    ReturnFreshAllocation {
        pointer_arg: usize,
        size_arg: usize,
        elem_size: u64,
    },
    /// `alloc::alloc::exchange_malloc(size, align)` — a fresh allocation of
    /// `size_arg` bytes, returned as `*mut u8`.
    ReturnExchangeMalloc { size_arg: usize },
    /// The return value is the length of an aggregate argument.
    ReturnLengthOfArg { arg: usize },
    /// The return value is `min(lhs_arg, rhs_arg)`, satisfying
    /// `return <= lhs_arg` and `return <= rhs_arg`.
    ReturnMin { lhs_arg: usize, rhs_arg: usize },
    /// The return value is `max(lhs_arg, rhs_arg)`.
    ReturnMax { lhs_arg: usize, rhs_arg: usize },
    /// The return value is `clamp(value_arg, min_arg, max_arg)`.
    ReturnClamp {
        value_arg: usize,
        min_arg: usize,
        max_arg: usize,
    },
    /// The return value is the absolute value of `arg` (`ite(arg >= 0, arg, -arg)`).
    ReturnAbs { arg: usize },
    /// The return value is the negation of `arg` (`-arg`).
    ReturnNeg { arg: usize },
    /// The return value is `lhs_arg + rhs_arg`.
    ReturnAdd { lhs_arg: usize, rhs_arg: usize },
    /// The return value is `lhs_arg * rhs_arg`.
    ReturnMul { lhs_arg: usize, rhs_arg: usize },
    /// The call returns `Option<T>` whose `Some` payload is `lhs_arg + rhs_arg`
    /// (models `checked_add`; the payload is non-zero whenever `lhs_arg` is).
    ReturnOptionSomeAdd { lhs_arg: usize, rhs_arg: usize },
    /// The call returns `Option<T>` whose `Some` payload is `lhs_arg * rhs_arg`
    /// (models `checked_mul`; the payload is non-zero whenever both args are).
    ReturnOptionSomeMul { lhs_arg: usize, rhs_arg: usize },
    /// The return value is non-zero *iff* `arg` is non-zero (models bit-preserving
    /// operations like `rotate_left`/`swap_bytes`/`count_ones`/`isqrt`, which map
    /// `0` to `0` and non-zero to non-zero).
    ReturnNonZeroIff { arg: usize },
    /// The call returns `Option<T>` whose `Some` payload is non-zero *iff* `arg`
    /// is non-zero (models `checked_pow`).
    ReturnOptionSomeNonZeroIff { arg: usize },
    /// The call returns `Option<T>` whose `Some` payload is unconditionally
    /// non-zero (models `checked_next_power_of_two`, where the next power of
    /// two is always positive regardless of the argument).
    ReturnOptionSomeNonZero,
    /// A specific field of the returned tuple is known to be non-zero (e.g.
    /// `overflowing_abs`/`overflowing_neg` return `(result, overflow)` where
    /// `result != 0`). Used to discharge a downstream `ValidNum(result != 0)`.
    ReturnTupleFieldNonZero { field: usize },
    /// A specific field of the returned tuple carries the length of a given
    /// argument (e.g. split_at(mid) returns (left, right) where left.len() == mid).
    ReturnTupleFieldLength { field: usize, from_arg: usize },
    /// The return value is a pointer backed by a fresh heap allocation of
    /// `size_arg` elements × `elem_size` bytes. Unlike ReturnFreshAllocation
    /// this does not require a pointer argument — used for constructors like
    /// `Vec::from_elem(init, count)` that allocate fresh memory.
    ReturnNewAllocation { size_arg: usize, elem_size: u64 },
    /// `Box::new` / `Box::new_in` / `Box::new_uninit` / `Box::new_uninit_in`
    /// (and `try_` variants): allocate a fresh heap buffer of `size_of::<T>()`
    /// bytes and return a `Box` whose pointer field backs it.  These have MIR
    /// available but carry a `match` on the allocator's `Result`, which the
    /// inline heuristic rejects as a semantic branch, so a direct effect is the
    /// only way the fresh allocation's provenance reaches the `NonNull`.
    ReturnBoxAllocation,
    /// Like ReturnNewAllocation but the length is carried by the argument
    /// itself (a Box fat pointer) rather than a separate count argument.
    /// Used for `into_vec` / `box_assume_init_into_vec_unsafe`.
    ReturnNewAllocationFromBox,
    /// Like `ReturnNewAllocation`, but the argument is the *capacity*: the
    /// returned Vec starts empty (`len == 0`) with `cap == cap_arg` (models
    /// `Vec::with_capacity`).
    ReturnNewAllocationFromCap { cap_arg: usize, elem_size: u64 },
    /// The return value is a non-zero power of two (models `Layout::align`).
    ReturnPowerOfTwo,
    /// The call transfers a Vec's backing allocation into a Box (e.g.
    /// `Vec::into_boxed_slice`). Looks up the current heap allocation from the
    /// argument's owning pointer field via its stack provenance.
    ReturnBoxFromVec { arg: usize },
    /// The return value is known to own initialized memory of the type pointed
    /// to by the indicated argument (e.g. `Box::from_raw(p)` owns one initialized
    /// `T` element reached through `p`).
    OwnsInitMemory { arg: usize },
    /// The call returns `Option<usize>` whose `Some` payload is a scan index
    /// into the iterator argument `self_arg` (models `Iterator::position` /
    /// `Iterator::find`): `Some(i)` satisfies `0 <= i < self.len()` where
    /// `self` is the Iter/IterMut struct produced by `into_iter`/`iter`.
    ReturnOptionSomeScanIndex { self_arg: usize },
    /// The call is `Try::branch`: `Option<T>` -> `ControlFlow<Option<!>, T>`,
    /// so the result's `Continue` payload (field 0) equals the input's `Some`
    /// payload (field 0).  Models the `?` operator's `if let Some(..) = expr?`
    /// unwrap so the payload's provenance survives the branch.
    ReturnBranchPayload { arg: usize },
    /// The call returns the length of a nul-terminated string (models
    /// `strlen`): `0 <= len < isize::MAX`, so `len + 1` (the byte length with
    /// the terminator) fits in `isize::MAX` — discharging the
    /// `from_raw_parts` `ValidNum(size_of(T)*(len+1) <= isize::MAX)` bound.
    ReturnScanLength,
    /// `ptr.align_offset(align)` returns an offset such that
    /// `(ptr + offset) % align == 0` and `0 <= offset < align` (or `usize::MAX`
    /// when no such offset exists). Models `*const T::align_offset` /
    /// `*mut T::align_offset` by recording the alignment path-condition so
    /// downstream `ptr.add(offset)` dereferences can discharge `Align`.
    ReturnAlignOffset { ptr_arg: usize, align_arg: usize },
    /// A local `align_to`-style wrapper (`align_to_ext`/`align_to_mut_ext`)
    /// returns `(prefix, body, suffix)` where `body` is `align_of::<U>()`-aligned.
    /// Models the tuple by creating three sub-slices whose lengths/offsets obey
    /// `prefix.len() = offset` and `len - suffix.len() = offset + k*size_of::<U>()`,
    /// and records `(ptr + offset) % align_of::<U>() == 0` so downstream
    /// `ptr.add(offset - k)` dereferences can discharge `Align`.
    ReturnAlignTo { receiver_arg: usize },
    /// `<ManuallyDrop<T> as Deref>::deref` / `MaybeDangling::as_ref` return a
    /// reference to the inner value at the *same* address (transparent
    /// wrappers).  The return aliases `arg` (a `&T` pointing at `arg`'s
    /// pointee) and its pointee field values are the argument's field values
    /// with the leading `peel` transparent field-0 hops stripped.
    ReturnTransparentDeref { arg: usize, peel: usize },
    /// `slice::range(range, bounds)` returns `Range { start, end }` satisfying
    /// `0 <= start <= end <= bounds.end`. Models the range normalizer whose
    /// `start_bound`/`end_bound` trait dispatch cannot be inlined.
    ReturnRange { bounds_arg: usize },
    /// `mem::replace(dest, src)` returns `*dest` (the old value), so the return
    /// is the *pointee* of the reference argument, not the reference itself.
    ReturnDerefArg { arg: usize },
    /// The call *frees* the heap allocation behind `pointer_arg` (a `&mut`
    /// reference to a `Box`/`Vec`/`String` pointee). Models `ManuallyDrop::drop`.
    DropMemory { pointer_arg: usize },
    /// `<[T]>::index(range)` / `::index_mut(range)` returns a sub-slice whose
    /// length is the range's extent. Modelled as a sub-allocation of the array
    /// so downstream `into_iter`/`next()` see the correct element count.
    ReturnSliceRangeIndex,
    /// `<[T]>::get(range)` / `::get_mut(range)` returns `Option<&[T]>` whose
    /// `Some` payload is a sub-slice with the range's extent.
    ReturnSliceRangeGet,
    /// `Iter::len()` / `Iter::is_empty()` computed from the iterator's pointer
    /// fields (`ptr` + `end_or_len` sharing the same allocation).
    ReturnIterLen { is_len: bool },
    /// `NonNull::<T>::new(ptr) -> Option<NonNull<T>>`: the safe constructor,
    /// returning `Some(ptr)` when the pointer is provably non-null and an
    /// unconstrained `Option` otherwise.
    ReturnNonNullNew,
    /// `Iter::next()` / `IterMut::next()`: return the current element pointer
    /// and advance the iterator's tracked offset by one.
    ReturnIterNext,
    /// `Range<A>::next` / `RangeInclusive<A>::next`: return the current
    /// `start` and advance it by one, carrying the `start < end` bound so a
    /// downstream `InBound(arr, i)` can be discharged.
    ReturnRangeNext,
    /// `size_of::<T>()` / `align_of::<T>()` for a *generic* `T` (no concrete
    /// layout): the result is the shared symbolic `sizeof_T` / `align_T`, bound
    /// at apply time from `func`'s type argument.
    ReturnLayoutSymbolic { is_size: bool },
}

/// Return dependency information for a MIR call terminator.
pub(crate) fn dependency_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    arg_count: usize,
    context: &CallContext,
) -> CallDependencySummary {
    let callee = mir_utils::dep_callee_def_id(func);

    // MIR dataflow first: works for local and cross-crate (`#[inline]`)
    // callees alike, no hand-written table needed.
    if let Some(callee) = callee {
        if tcx.intrinsic(callee).is_some() || mir_utils::is_drop_in_place(callee) {
            return CallDependencySummary::unknown(arg_count);
        }
        if let Some(must_write_args) = interprocedural::local_must_write_args(tcx, callee, context)
            && !must_write_args.is_empty() {
                return CallDependencySummary {
                    return_depends_on_args: Vec::new(),
                    must_write_args: must_write_args
                        .into_iter()
                        .filter(|index| *index < arg_count)
                        .collect(),
                    unsupported: false,
                };
            }
        // `Try::branch` (`Option<T>` -> `ControlFlow<Option<!>, T>`): the
        // `Continue` payload is the input's `Some` payload, so the return value
        // depends on the input.  Matched by `DefId` (the trait method's `self`
        // type is generic, so the type check below is skipped here).
        if is_branch(Some(callee)) {
            return CallDependencySummary {
                return_depends_on_args: vec![0],
                must_write_args: Vec::new(),
                unsupported: false,
            };
        }
        if let Some(return_deps) = interprocedural::local_return_dependencies(tcx, callee) {
            return CallDependencySummary {
                return_depends_on_args: return_deps
                    .into_iter()
                    .filter(|index| *index < arg_count)
                    .collect(),
                must_write_args: Vec::new(),
                unsupported: false,
            };
        }
    }

    CallDependencySummary::unknown(arg_count)
}

/// Non-registry effect fallback for a MIR call terminator: the
/// transparent-wrapper deref, otherwise unknown. The registry lookup itself runs
/// earlier in `exec_call` so it can also gate inlining.
pub(crate) fn effect_summary<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> CallEffectSummary {
    // Transparent-wrapper deref: `<ManuallyDrop<T> as Deref>::deref` /
    // `deref_mut` (and `MaybeDangling::as_ref`/`as_mut`) return a reference to
    // the inner value at the same address.  The std MIR for these is
    // unavailable cross-crate, so model them with field-value peeling.
    if let Some(peel) = transparent_deref_peel(tcx, func) {
        return CallEffectSummary {
            effects: vec![CallEffect::ReturnTransparentDeref { arg: 0, peel }],
            unsupported: false,
        };
    }

    CallEffectSummary::unknown()
}

/// Detect a transparent-wrapper deref whose receiver is `ManuallyDrop<T>` or
/// `MaybeDangling<T>`, and return how many leading field-0 hops must be peeled
/// to reach the inner `T`:
///   * `ManuallyDrop<T> { value: MaybeDangling<T> }` → 2 (`value` → `MaybeDangling.0`)
///   * `MaybeDangling<P>(P)` → 1.
fn transparent_deref_peel<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<usize> {
    let self_ty = mir_utils::fn_def_first_type_arg(func)?;
    let TyKind::Adt(adt_def, _) = self_ty.kind() else {
        return None;
    };
    let did = adt_def.did();
    if tcx.is_lang_item(did, LangItem::ManuallyDrop) {
        return Some(2);
    }
    if is_maybe_dangling(tcx, did) {
        return Some(1);
    }
    None
}

/// Whether `did` is the `MaybeDangling` lang item.
///
/// The `MaybeDangling` lang item was only added to rustc's table after
/// nightly-2026-02-05 (the `verify-std` toolchain), so gate the lang-item
/// lookup behind a build-time check and fall back to name matching on
/// toolchains that lack it.
fn is_maybe_dangling(tcx: TyCtxt<'_>, did: DefId) -> bool {
    #[cfg(rapx_has_maybe_dangling_lang_item)]
    {
        tcx.is_lang_item(did, LangItem::MaybeDangling)
    }
    #[cfg(not(rapx_has_maybe_dangling_lang_item))]
    {
        tcx.def_path_str(did).contains("MaybeDangling")
    }
}

// ── Collection element-size helpers ──────────────────────────────
// Used by [`builtin_models`] and the VM to size `from_raw_parts`/`Vec`
// results; moved here from `helpers::mir_utils` because they depend on the
// [`crate::verify::api_classify`] classifiers.

/// Element type of a `Vec<T>`, if `ty` is a `Vec`.
pub(crate) fn vec_elem_ty<'tcx>(_tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    if let TyKind::Adt(adt_def, substs) = ty.kind()
        && is_std_vec(adt_def.did()) {
            return substs.first().and_then(|s| s.as_type());
        }
    None
}

/// Element type of a `from_raw_parts` result: `&[T]`/`*[T]`/`Vec<T>` yield `T`;
/// other types (including `String`) return `None`.
pub(crate) fn from_raw_parts_elem_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> Option<Ty<'tcx>> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    match ty.kind() {
        TyKind::Ref(_, inner, _) => match inner.kind() {
            TyKind::Slice(e) => Some(*e),
            _ => None,
        },
        TyKind::RawPtr(inner, _) => match inner.kind() {
            TyKind::Slice(e) => Some(*e),
            _ => None,
        },
        TyKind::Adt(..) => vec_elem_ty(tcx, ty),
        _ => None,
    }
}

/// Element size of a `from_raw_parts` result. Covers `&[T]`/`*[T]` (borrowed
/// slice) and `Vec<T>` (owned); `String` and unknown layouts fall back to 1
/// (`String`'s element is `u8`, so 1 is correct).
pub(crate) fn from_raw_parts_elem_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> u64 {
    from_raw_parts_elem_ty(tcx, caller, dest)
        .and_then(|e| mir_utils::type_layout(tcx, caller, e).map(|(_, s)| s))
        .unwrap_or(1)
}
