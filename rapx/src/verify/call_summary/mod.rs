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
pub mod fn_simulator;
pub mod interprocedural;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Operand},
    ty::{GenericArgKind, TyCtxt, TyKind},
};

use crate::helpers::mir_utils;

/// Dependency summary consumed by the backward visitor.
#[derive(Clone, Debug)]
pub struct CallDependencySummary {
    /// Callee definition when the call target is statically known.
    pub callee: Option<DefId>,
    /// Human-readable callee name.
    pub name: String,
    /// If the call destination is relevant, these call arguments are relevant.
    pub return_depends_on_args: Vec<usize>,
    /// Arguments that may be written or invalidated by the call.
    pub may_write_args: Vec<usize>,
    /// True when this summary is conservative rather than precise.
    pub unsupported: bool,
}

impl CallDependencySummary {
    /// Build a conservative summary that keeps all arguments relevant.
    fn unknown(callee: Option<DefId>, name: String, arg_count: usize) -> Self {
        Self {
            callee,
            name,
            return_depends_on_args: (0..arg_count).collect(),
            may_write_args: Vec::new(),
            unsupported: true,
        }
    }
}

/// Effect summary consumed by the forward visitor.
#[derive(Clone, Debug)]
pub struct CallEffectSummary {
    /// Callee definition when the call target is statically known.
    pub callee: Option<DefId>,
    /// Human-readable callee name.
    pub name: String,
    /// Destination local receiving the return value.
    pub destination: Option<Local>,
    /// Effects that can be applied to the path-local abstract state.
    pub effects: Vec<CallEffect>,
    /// True when this summary is conservative rather than precise.
    pub unsupported: bool,
}

impl CallEffectSummary {
    /// Build a conservative summary for an unsupported call.
    fn unknown(callee: Option<DefId>, name: String, destination: Option<Local>) -> Self {
        Self {
            callee,
            name,
            destination,
            effects: Vec::new(),
            unsupported: true,
        }
    }
}

/// Path-local effect produced by a retained call.
#[derive(Clone, Debug)]
pub enum CallEffect {
    /// The return value aliases or is a direct value flow from an argument.
    ReturnAliasArg { arg: usize },
    /// The return value is a pointer extracted from an aggregate/reference arg.
    ReturnPointerFromArg { arg: usize },
    /// The return value is `base + offset * stride`.
    ReturnPointerAdd {
        base_arg: usize,
        offset_arg: usize,
        stride: Option<u64>,
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
    ReturnAligned { align: u64, ty_name: String },
    /// The return value is a concrete layout/numeric constant.
    ReturnConst { value: u64, label: String },
    /// The call reads memory through an argument.
    ReadMemory { arg: usize },
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
    /// The return value is the length of an aggregate argument.
    ReturnLengthOfArg { arg: usize },
    /// The return value is `1` iff the length of the aggregate argument is 0.
    ReturnIsEmptyOfArg { arg: usize },
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
    /// Like ReturnNewAllocation but the length is carried by the argument
    /// itself (a Box fat pointer) rather than a separate count argument.
    /// Used for `into_vec` / `box_assume_init_into_vec_unsafe`.
    ReturnNewAllocationFromBox { box_arg: usize },
    /// `Allocator::allocate(self, layout)` / `allocate_zeroed` returns a
    /// `Result<NonNull<[u8]>, AllocError>`. Model the `Ok` variant as a fresh
    /// *external* (unbounded) allocation so downstream `NonNull`/`Allocated`
    /// checks auto-pass regardless of the symbolic `layout.size()`. The
    /// `Result` downcast (`((result as Ok).0)`) then propagates the provenance.
    ReturnAllocBuffer,
    /// The return value is a non-zero power of two (models `Layout::align`).
    ReturnPowerOfTwo,
    /// The call transfers a Vec's backing allocation into a Box (e.g.
    /// `Vec::into_boxed_slice`). Looks up the current heap allocation from
    /// the allocation's `slice_data` via the argument's stack provenance.
    ReturnBoxFromVec { arg: usize },
    /// The return value is known to own initialized memory of the type pointed
    /// to by the indicated argument (e.g. `Box::from_raw(p)` owns one initialized
    /// `T` element reached through `p`).
    OwnsInitMemory { arg: usize },
    /// The call validates that every element of the array argument `indices_arg`
    /// is `< args[len_arg]` and that the elements are pairwise distinct, returning
    /// `Err` otherwise.  On the `Ok` continuation the caller may assume
    /// `InBound(index_access(slice_of(len_arg), indices_arg))` and
    /// `NonOverlap(indices_arg)`.  (A trusted interprocedural summary, like the
    /// std-primitive summaries — the validator's body is not re-proved here.)
    ChecksIndexBoundsDisjoint { indices_arg: usize, len_arg: usize },
    /// The call returns `Option<usize>` whose `Some` payload is a scan index
    /// into the iterator argument `self_arg` (models `Iterator::position` /
    /// `Iterator::find`): `Some(i)` satisfies `0 <= i < self.len()` where
    /// `self` is the Iter/IterMut struct produced by `into_iter`/`iter`.
    ReturnOptionSomeScanIndex { self_arg: usize },
    /// The call returns the length of a nul-terminated string (models
    /// `strlen`): `0 <= len < isize::MAX`, so `len + 1` (the byte length with
    /// the terminator) fits in `isize::MAX` — discharging the
    /// `from_raw_parts` `ValidNum(size_of(T)*(len+1) <= isize::MAX)` bound.
    ReturnScanLength { ptr_arg: usize },
    /// Remove the allocation's `slice_data` link for the argument's stack
    /// alloc_id — used for `mem::forget` which prevents a drop cascade.
    CleanSliceDataLinks { arg: usize },
    /// Returns the element-count distance between two pointers with common
    /// provenance: `(self_arg.addr() - origin_arg.addr()) / sizeof(T)`.
    /// Models `NonNull::offset_from_unsigned` / `offset_from`.
    ReturnOffsetFromUnsigned { self_arg: usize, origin_arg: usize },
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
    /// `IntoIterator::into_iter` on `&[T]` / `&mut [T]` returns an
    /// `Iter`/`IterMut` whose `ptr` (field 0) and `end_or_len` (field 1) share
    /// the source slice's allocation. Models the constructor by materializing
    /// those two pointer fields so downstream `Iterator::next` / `len` /
    /// `is_empty` can resolve the iterator's provenance and element type.
    ReturnIter { receiver_arg: usize },
    /// `<ManuallyDrop<T> as Deref>::deref` / `MaybeDangling::as_ref` return a
    /// reference to the inner value at the *same* address (transparent
    /// wrappers).  The return aliases `arg` (a `&T` pointing at `arg`'s
    /// pointee) and its pointee field values are the argument's field values
    /// with the leading `peel` transparent field-0 hops stripped.
    ReturnTransparentDeref { arg: usize, peel: usize },
}

/// Return dependency information for a MIR call terminator.
pub fn dependency_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    arg_count: usize,
) -> CallDependencySummary {
    let callee = mir_utils::dep_callee_def_id(func);
    let name = mir_utils::call_name(tcx, func);

    if let Some(summary) = fn_simulator::lookup_dependency(callee, &name, arg_count) {
        return summary;
    }

    // Interprocedural fallback for local callees.
    if let Some(callee) = callee {
        if name.contains("::intrinsics::")
            || name.starts_with("intrinsics::")
            || name.ends_with("::drop_in_place")
        {
            return CallDependencySummary::unknown(Some(callee), name, arg_count);
        }
        if let Some(must_write_args) = interprocedural::local_must_write_args(tcx, callee) {
            if !must_write_args.is_empty() {
                return CallDependencySummary {
                    callee: Some(callee),
                    name,
                    return_depends_on_args: Vec::new(),
                    may_write_args: must_write_args
                        .into_iter()
                        .filter(|index| *index < arg_count)
                        .collect(),
                    unsupported: false,
                };
            }
        }
        if let Some(return_deps) = interprocedural::local_return_dependencies(tcx, callee) {
            return CallDependencySummary {
                callee: Some(callee),
                name,
                return_depends_on_args: return_deps
                    .into_iter()
                    .filter(|index| *index < arg_count)
                    .collect(),
                may_write_args: Vec::new(),
                unsupported: false,
            };
        }
    }

    CallDependencySummary::unknown(callee, name, arg_count)
}

/// Return effect information for a MIR call terminator.
pub fn effect_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
    destination: Local,
) -> CallEffectSummary {
    let callee = mir_utils::dep_callee_def_id(func);
    let name = mir_utils::call_name(tcx, func);

    if let Some(summary) = fn_simulator::lookup_effect(tcx, caller, callee, &name, func, destination) {
        return summary;
    }

    // Transparent-wrapper deref: `<ManuallyDrop<T> as Deref>::deref` /
    // `deref_mut` (and `MaybeDangling::as_ref`/`as_mut`) return a reference to
    // the inner value at the same address.  The std MIR for these is
    // unavailable cross-crate, so model them with field-value peeling.
    if let Some(peel) = transparent_deref_peel(tcx, func) {
        return CallEffectSummary {
            callee,
            name,
            destination: Some(destination),
            effects: vec![CallEffect::ReturnTransparentDeref { arg: 0, peel }],
            unsupported: false,
        };
    }

    // Interprocedural fallback for local callees.
    if let Some(callee) = callee {
        if name.contains("::intrinsics::")
            || name.starts_with("intrinsics::")
            || name.ends_with("::drop_in_place")
        {
            return CallEffectSummary::unknown(Some(callee), name, Some(destination));
        }
        if let Some(must_write_args) = interprocedural::local_must_write_args(tcx, callee) {
            let effects: Vec<_> = must_write_args
                .into_iter()
                .map(|arg| CallEffect::WriteMemory { pointer_arg: arg })
                .collect();
            if !effects.is_empty() {
                return CallEffectSummary {
                    callee: Some(callee),
                    name,
                    destination: Some(destination),
                    effects,
                    unsupported: false,
                };
            }
        }
        if let Some(effect) = interprocedural::try_pointer_arith_wrapper_effect(tcx, callee, Some(destination)) {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination: Some(destination),
                effects: vec![effect],
                unsupported: false,
            };
        }
        if let Some(effect) = interprocedural::try_from_raw_parts_wrapper_effect(tcx, callee, Some(destination)) {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination: Some(destination),
                effects: vec![effect],
                unsupported: false,
            };
        }
        if let Some((indices_arg, len_arg)) = interprocedural::detect_index_disjoint_validator(tcx, callee)
            .or_else(|| interprocedural::named_index_disjoint_validator(&name))
        {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination: Some(destination),
                effects: vec![CallEffect::ChecksIndexBoundsDisjoint {
                    indices_arg,
                    len_arg,
                }],
                unsupported: false,
            };
        }
        if let Some(return_deps) = interprocedural::local_return_dependencies(tcx, callee) {
            // If the callee does pointer arithmetic, don't produce ReturnAliasArg
            // since the offset might have been changed (e.g. wrapping_add(1)).
            if !interprocedural::callee_contains_pointer_arithmetic(tcx, callee) {
                // If the callee transitively calls functions that may write
                // through &mut args, ReturnAliasArg alone is insufficient —
                // the writes are lost. Mark as unsupported so CalleeEntry
                // DFS can inline the full body.
                let has_nested_calls = interprocedural::callee_calls_other_local(tcx, callee);
                return CallEffectSummary {
                    callee: Some(callee),
                    name,
                    destination: Some(destination),
                    effects: return_deps
                        .into_iter()
                        .map(|arg| CallEffect::ReturnAliasArg { arg })
                        .collect(),
                    unsupported: has_nested_calls,
                };
            }
        }
    }

    CallEffectSummary::unknown(callee, name, Some(destination))
}

/// Detect a transparent-wrapper deref whose receiver is `ManuallyDrop<T>` or
/// `MaybeDangling<T>`, and return how many leading field-0 hops must be peeled
/// to reach the inner `T`:
///   * `ManuallyDrop<T> { value: MaybeDangling<T> }` → 2 (`value` → `MaybeDangling.0`)
///   * `MaybeDangling<P>(P)` → 1.
fn transparent_deref_peel<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<usize> {
    let Operand::Constant(c) = func else { return None };
    let TyKind::FnDef(_, args) = c.const_.ty().kind() else { return None };
    let self_ty = args.iter().find_map(|a| {
        #[cfg(rapx_ge_99)] let a = a.skip_binder();
        if let GenericArgKind::Type(t) = a.kind() { Some(t) } else { None }
    })?;
    let TyKind::Adt(adt_def, _) = self_ty.kind() else { return None };
    let path = tcx.def_path_str(adt_def.did());
    if path.contains("ManuallyDrop") {
        Some(2)
    } else if path.contains("MaybeDangling") {
        Some(1)
    } else {
        None
    }
}

