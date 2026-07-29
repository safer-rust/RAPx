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
    ty::{Ty, TyCtxt, TyKind},
};

use super::slicer::ForgetReason;
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
    /// The return value is the length of an aggregate argument.
    ReturnLengthOfArg { arg: usize },
    /// The return value is `1` iff the length of the aggregate argument is 0.
    ReturnIsEmptyOfArg { arg: usize },
    /// The return value is `min(lhs_arg, rhs_arg)`, satisfying
    /// `return <= lhs_arg` and `return <= rhs_arg`.
    ReturnMin { lhs_arg: usize, rhs_arg: usize },
    /// A specific field of the returned tuple carries the length of a given
    /// argument (e.g. split_at(mid) returns (left, right) where left.len() == mid).
    ReturnTupleFieldLength { field: usize, from_arg: usize },
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
    /// The call returns a `Range { start, end }` guaranteed to satisfy
    /// `0 <= start <= end <= bounds`, where `bounds` is the `end` field (field 0)
    /// of the `RangeTo` argument at `bounds_arg`.  Models `core::slice::range`,
    /// whose result feeds subslice pointer arithmetic in callers such as
    /// `slice::copy_within`.
    ReturnBoundedRange { bounds_arg: usize },
    /// `align_to_offsets` returns `(us_len, ts_len)` where field 0 <=
    /// `receiver.len()` / ts and field 1 < ts, ensuring the remaining
    /// pointer arithmetic stays in bounds on the tail.
    ReturnLcmSplit { receiver_arg: usize },
    /// Facts about an argument must be forgotten conservatively.
    ForgetArgFacts { arg: usize, reason: ForgetReason },
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
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination: Some(destination),
                effects: return_deps
                    .into_iter()
                    .map(|arg| CallEffect::ReturnAliasArg { arg })
                    .collect(),
                unsupported: false,
            };
        }
    }

    CallEffectSummary::unknown(callee, name, Some(destination))
}

/// Return true when every argument type is *layout-safe*: passing such a value
/// to an unsupported call cannot let that call change any slice's length or
/// base address, reallocate, or free memory.  Scalars, `str`, slices, arrays,
/// generic type parameters (elements, closures), closures, and references or
/// tuples of these are layout-safe; raw pointers and concrete owning
/// containers (`Vec`, `Box`, `String`, collections, other ADTs) are not.
pub fn call_args_preserve_layout<'tcx>(arg_tys: impl Iterator<Item = Ty<'tcx>>) -> bool {
    arg_tys.map(|ty| ty_is_layout_safe_inner(ty, 0)).all(|safe| safe)
}

fn ty_is_layout_safe_inner(ty: Ty<'_>, depth: usize) -> bool {
    if depth > 6 {
        return false;
    }
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str
        | TyKind::Param(_)
        | TyKind::Closure(..)
        | TyKind::Never => true,
        TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            ty_is_layout_safe_inner(*inner, depth + 1)
        }
        // A shared reference can never reallocate, free, or reassign the
        // callee's length-carrying storage (the callee holds a copy of the
        // fat pointer; interior mutability can change contents but not the
        // length/base of a slice we track).  A mutable reference can only do
        // so if it points at an owning container, so recurse into the pointee.
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not) => true,
        TyKind::Ref(_, inner, rustc_middle::ty::Mutability::Mut) => {
            ty_is_layout_safe_inner(*inner, depth + 1)
        }
        TyKind::Tuple(elems) => elems.iter().all(|e| ty_is_layout_safe_inner(e, depth + 1)),
        // Raw pointers, FnDef, and concrete ADTs (Vec/Box/String/collections/…)
        // may reallocate, free, or reassign length-carrying storage.
        _ => false,
    }
}

