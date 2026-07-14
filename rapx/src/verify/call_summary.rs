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

use std::collections::HashSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{ConstKind, GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path_analysis::graph::{PathEnumerator, PathGraph};

use super::{primitive::PrimitiveCall, slicer::ForgetReason};

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
    /// A specific field of the returned tuple carries the length of a given
    /// argument (e.g. split_at(mid) returns (left, right) where left.len() == mid).
    ReturnTupleFieldLength { field: usize, from_arg: usize },
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
    let callee = callee_def_id(func);
    let name = call_name(tcx, func);

    let primitive = PrimitiveCall::classify(&name);

    if primitive.is_some_and(PrimitiveCall::is_as_ptr_like) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::AsPtrRange)
        || primitive == Some(PrimitiveCall::AsMutPtrRange)
    {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive.is_some_and(PrimitiveCall::is_pointer_arithmetic) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0, 1],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::PtrRead) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::PtrWrite) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: Vec::new(),
            may_write_args: vec![0],
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::Len) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::MaybeUninitUninit) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: Vec::new(),
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::NumericArith) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: (0..arg_count).collect(),
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_slice_range_fn(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0, 1],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_align_to_offsets_fn(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: (0..arg_count).collect(),
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::OptionUnwrap) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if primitive.is_some_and(PrimitiveCall::is_layout_constant) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: Vec::new(),
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if let Some(prim) = primitive
        && matches!(prim, PrimitiveCall::SplitAt | PrimitiveCall::SplitAtMut)
    {
        // The returned prefix/suffix slices depend both on the source buffer
        // (arg 0) and on the split point `mid` (arg 1); the prefix length is
        // exactly `mid`.  Keep both so the backward slice retains the `mid`
        // computation for downstream `len(prefix)` obligations.
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0, 1],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_from_trait_call(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if let Some(callee) = callee {
        // Skip interprocedural analysis for intrinsics and
        // compiler-generated functions — their MIR can trigger
        // worker-thread stack overflows during `optimized_mir`.
        if name.contains("::intrinsics::")
            || name.starts_with("intrinsics::")
            || name.ends_with("::drop_in_place")
        {
            return CallDependencySummary::unknown(Some(callee), name, arg_count);
        }
        if let Some(must_write_args) = local_must_write_args(tcx, callee) {
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
        if let Some(return_deps) = local_return_dependencies(tcx, callee) {
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
    let callee = callee_def_id(func);
    let name = call_name(tcx, func);
    let destination = Some(destination);

    let primitive = PrimitiveCall::classify(&name);

    if primitive.is_some_and(PrimitiveCall::is_as_ptr_like) {
        let mut effects = vec![
            CallEffect::ReturnPointerFromArg { arg: 0 },
            CallEffect::ReturnNonZero,
        ];
        if let Some((align, ty_name)) = destination_pointee_alignment(tcx, caller, destination) {
            effects.push(CallEffect::ReturnAligned { align, ty_name });
        }
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects,
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::AsPtrRange)
        || primitive == Some(PrimitiveCall::AsMutPtrRange)
    {
        let effects = vec![CallEffect::ReturnAliasArg { arg: 0 }];
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects,
            unsupported: false,
        };
    }

    if primitive.is_some_and(PrimitiveCall::is_pointer_add_like) {
        let stride = if primitive.is_some_and(PrimitiveCall::is_byte_pointer_arithmetic) {
            Some(1)
        } else {
            destination_stride(tcx, caller, destination)
        };
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnPointerAdd {
                base_arg: 0,
                offset_arg: 1,
                stride,
            }],
            unsupported: false,
        };
    }

    if primitive.is_some_and(PrimitiveCall::is_pointer_sub_like) {
        let stride = if primitive.is_some_and(PrimitiveCall::is_byte_pointer_arithmetic) {
            Some(1)
        } else {
            destination_stride(tcx, caller, destination)
        };
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnPointerSub {
                base_arg: 0,
                offset_arg: 1,
                stride,
            }],
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::PtrRead) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReadMemory { arg: 0 }],
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::PtrWrite) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::WriteMemory { pointer_arg: 0 }],
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::Len) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnLengthOfArg { arg: 0 }],
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::MaybeUninitUninit) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::NumericArith) {
        // Pure arithmetic: no memory effect and never precision-losing.  The
        // SMT model reconstructs the exact product/sum from the operands (see
        // the `unchecked_mul` handling in `assert_forward_facts`).
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: Vec::new(),
            unsupported: false,
        };
    }

    if primitive == Some(PrimitiveCall::OptionUnwrap) {
        // `expect`/`unwrap` extract the wrapped payload with no memory effect;
        // the value is recovered from the receiver in `term_for_value_at`.
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: Vec::new(),
            unsupported: false,
        };
    }

    if is_slice_range_fn(&name) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnBoundedRange { bounds_arg: 1 }],
            unsupported: false,
        };
    }

    if is_align_to_offsets_fn(&name) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnLcmSplit { receiver_arg: 0 }],
            unsupported: false,
        };
    }

    if primitive.is_some_and(PrimitiveCall::is_layout_constant) {
        let effects = layout_constant_effect(tcx, caller, func, &name)
            .into_iter()
            .collect();
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects,
            unsupported: false,
        };
    }

    if let Some(prim) = primitive
        && matches!(prim, PrimitiveCall::SplitAt | PrimitiveCall::SplitAtMut)
    {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnTupleFieldLength {
                field: 0,
                from_arg: 1,
            }],
            unsupported: false,
        };
    }

    if let Some(prim) = primitive
        && matches!(
            prim,
            PrimitiveCall::FromRawParts | PrimitiveCall::FromRawPartsMut
        )
    {
        let mut effects = vec![
            CallEffect::ReturnAliasArg { arg: 0 },
            CallEffect::ReturnNonZero,
        ];
        if let Some((align, ty_name)) = destination_pointee_alignment(tcx, caller, destination) {
            effects.push(CallEffect::ReturnAligned { align, ty_name });
        }
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects,
            unsupported: false,
        };
    }

    if is_from_trait_call(&name) && is_nonnull_destination(tcx, caller, destination) {
        let mut effects = vec![
            CallEffect::ReturnPointerFromArg { arg: 0 },
            CallEffect::ReturnNonZero,
        ];
        if let Some((align, ty_name)) = destination_nonnull_alignment(tcx, caller, destination) {
            effects.push(CallEffect::ReturnAligned { align, ty_name });
        }
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects,
            unsupported: false,
        };
    }

    if let Some(callee) = callee {
        // Skip interprocedural analysis for intrinsics and
        // compiler-generated functions.
        if name.contains("::intrinsics::")
            || name.starts_with("intrinsics::")
            || name.ends_with("::drop_in_place")
        {
            return CallEffectSummary::unknown(Some(callee), name, destination);
        }
        if let Some(must_write_args) = local_must_write_args(tcx, callee) {
            let effects: Vec<_> = must_write_args
                .into_iter()
                .map(|arg| CallEffect::WriteMemory { pointer_arg: arg })
                .collect();
            if !effects.is_empty() {
                return CallEffectSummary {
                    callee: Some(callee),
                    name,
                    destination,
                    effects,
                    unsupported: false,
                };
            }
        }
        if let Some(effect) = try_pointer_arith_wrapper_effect(tcx, callee, destination) {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination,
                effects: vec![effect],
                unsupported: false,
            };
        }
        if let Some((indices_arg, len_arg)) = detect_index_disjoint_validator(tcx, callee)
            .or_else(|| named_index_disjoint_validator(&name))
        {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination,
                effects: vec![CallEffect::ChecksIndexBoundsDisjoint {
                    indices_arg,
                    len_arg,
                }],
                unsupported: false,
            };
        }
        if let Some(return_deps) = local_return_dependencies(tcx, callee) {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination,
                effects: return_deps
                    .into_iter()
                    .map(|arg| CallEffect::ReturnAliasArg { arg })
                    .collect(),
                unsupported: false,
            };
        }
    }

    CallEffectSummary::unknown(callee, name, destination)
}

/// Return the static callee definition for a MIR call operand.
pub fn callee_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(func_constant) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = func_constant.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

/// Return true when every argument type is *layout-safe*: passing such a value
/// to an unsupported call cannot let that call change any slice's length or
/// base address, reallocate, or free memory.  Scalars, `str`, slices, arrays,
/// generic type parameters (elements, closures), closures, and references or
/// tuples of these are layout-safe; raw pointers and concrete owning
/// containers (`Vec`, `Box`, `String`, collections, other ADTs) are not.
pub fn call_args_preserve_layout<'tcx>(arg_tys: impl Iterator<Item = Ty<'tcx>>) -> bool {
    arg_tys.map(ty_is_layout_safe_arg).all(|safe| safe)
}

/// See [`call_args_preserve_layout`].
pub fn ty_is_layout_safe_arg(ty: Ty<'_>) -> bool {
    ty_is_layout_safe_inner(ty, 0)
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

/// Return a stable, human-readable name for a MIR call operand.
pub fn call_name(tcx: TyCtxt<'_>, func: &Operand<'_>) -> String {
    callee_def_id(func)
        .map(|def_id| tcx.def_path_str(def_id))
        .unwrap_or_else(|| format!("{func:?}"))
}

/// Return true for slice/string/vector pointer extraction calls.
pub fn is_as_ptr_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::AsPtr)
}

/// Return true for mutable pointer extraction calls.
pub fn is_as_mut_ptr_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::AsMutPtr)
}

/// Return true for typed pointer addition calls.
pub fn is_pointer_add_call(name: &str) -> bool {
    PrimitiveCall::classify(name).is_some_and(PrimitiveCall::is_pointer_add_like)
}

/// Return true for typed pointer subtraction calls.
pub fn is_pointer_sub_call(name: &str) -> bool {
    PrimitiveCall::classify(name).is_some_and(PrimitiveCall::is_pointer_sub_like)
}

/// Return true for typed pointer offset calls.
pub fn is_pointer_offset_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::PtrOffset)
}

/// Return true for pointer reads.
pub fn is_pointer_read_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::PtrRead)
}

/// Return true for pointer writes that initialize one element.
pub fn is_pointer_write_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::PtrWrite)
}

/// Return true for slice/string/vector length queries.
pub fn is_len_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::Len)
}

/// Return true for `MaybeUninit::<T>::uninit`.
pub fn is_maybe_uninit_uninit_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::MaybeUninitUninit)
}

/// Return true for layout constant producers.
pub fn is_layout_constant_call(name: &str) -> bool {
    PrimitiveCall::classify(name).is_some_and(PrimitiveCall::is_layout_constant)
}

fn is_from_trait_call(name: &str) -> bool {
    name == "std::convert::From::from" || name == "core::convert::From::from"
}

/// Return a concrete layout constant effect for `align_of::<T>()` or `size_of::<T>()`.
fn layout_constant_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
    name: &str,
) -> Option<CallEffect> {
    let ty = layout_call_ty(func)?;
    let (align, size) = type_layout(tcx, caller, ty)?;
    match PrimitiveCall::classify(name)? {
        PrimitiveCall::AlignOf => Some(CallEffect::ReturnConst {
            value: align,
            label: format!("align_of::<{ty:?}>()"),
        }),
        PrimitiveCall::SizeOf => Some(CallEffect::ReturnConst {
            value: size,
            label: format!("size_of::<{ty:?}>()"),
        }),
        _ => None,
    }
}

/// Return the type argument for a layout-producing call.
fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(func_constant) = func else {
        return None;
    };
    let TyKind::FnDef(_, args) = func_constant.const_.ty().kind() else {
        return None;
    };
    args.iter().find_map(|arg| {
        #[cfg(rapx_rustc_ge_199)]
        let arg = arg.skip_binder();
        match arg.kind() {
        GenericArgKind::Type(ty) => Some(ty),
        _ => None,
    }
    })
}

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast
/// assignments to the outer callee's argument local, returning its index.
fn trace_to_callee_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &Operand<'_>,
) -> Option<usize> {
    use std::collections::{HashSet, VecDeque};

    let local = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        _ => return None,
    };
    let idx = local.as_usize();
    if idx >= 1 && idx <= body.arg_count {
        return Some(idx - 1);
    }
    let mut queue = VecDeque::from([local]);
    let mut seen = HashSet::from([local]);
    while let Some(current) = queue.pop_front() {
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            return Some(cidx - 1);
        }
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let dest = assign.0.local;
                if dest != current {
                    continue;
                }
                let source = match &assign.1 {
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::Cast(_, Operand::Copy(place), _)
                    | Rvalue::Cast(_, Operand::Move(place), _)
                    | Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => place.local,
                    _ => continue,
                };
                if !seen.contains(&source) {
                    seen.insert(source);
                    queue.push_back(source);
                }
            }
            let Some(terminator) = &bb.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            else {
                continue;
            };
            if destination.local != current {
                continue;
            }
            let primitive = PrimitiveCall::classify(&call_name(tcx, func));
            if !primitive.is_some_and(PrimitiveCall::is_as_ptr_like) {
                continue;
            }
            let Some(source) = args.first().and_then(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                Operand::Constant(_) => None,
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => None,
            }) else {
                continue;
            };
            if !seen.contains(&source) {
                seen.insert(source);
                queue.push_back(source);
            }
        }
    }
    None
}

/// Detect when a local callee wraps a pointer-arithmetic call (add/sub) and
/// produce the correct `ReturnPointerAdd` / `ReturnPointerSub` effect.
fn try_pointer_arith_wrapper_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    _destination: Option<Local>,
) -> Option<CallEffect> {
    use std::collections::{HashSet, VecDeque};

    if !tcx.is_mir_available(callee) {
        return None;
    }

    // Skip functions whose MIR is too large — they're unlikely to be
    // simple pointer-arithmetic wrappers and can trigger worker-thread
    // stack overflows during `optimized_mir`.
    let body = tcx.optimized_mir(callee);
    if body.basic_blocks.len() > 16 {
        return None;
    }
    let ret = Local::from_usize(0);

    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination: call_dest,
            ..
        } = &terminator.kind
        else {
            continue;
        };

        let name = call_name(tcx, func);
        let primitive = PrimitiveCall::classify(&name);
        let is_add = primitive.is_some_and(PrimitiveCall::is_pointer_add_like);
        let is_sub = primitive.is_some_and(PrimitiveCall::is_pointer_sub_like);

        // Also check if the inner callee is itself a pointer-arithmetic wrapper.
        let inner_effect = if !is_add && !is_sub {
            callee_def_id(func).and_then(|inner_callee| {
                let inner_name = call_name(tcx, func);
                if inner_name.contains("::intrinsics::")
                    || inner_name.starts_with("intrinsics::")
                    || inner_name.ends_with("::drop_in_place")
                {
                    return None;
                }
                try_pointer_arith_wrapper_effect(tcx, inner_callee, Some(call_dest.local))
            })
        } else {
            None
        };

        if !is_add && !is_sub && inner_effect.is_none() {
            continue;
        }

        // Check that the call result flows to the return value.
        let mut queue = VecDeque::from([call_dest.local]);
        let mut seen = HashSet::from([call_dest.local]);
        let mut reaches_ret = false;
        while let Some(current) = queue.pop_front() {
            if current == ret {
                reaches_ret = true;
                break;
            }
            for bb2 in body.basic_blocks.iter() {
                for stmt in &bb2.statements {
                    let StatementKind::Assign(assign) = &stmt.kind else {
                        continue;
                    };
                    let dest = assign.0.local;
                    if seen.contains(&dest) {
                        continue;
                    }
                    match &assign.1 {
                        Rvalue::Use(Operand::Copy(place), ..)
                        | Rvalue::Use(Operand::Move(place), ..) => {
                            if place.local == current {
                                queue.push_back(dest);
                                seen.insert(dest);
                            }
                        }
                        Rvalue::Cast(_, Operand::Copy(place), _)
                        | Rvalue::Cast(_, Operand::Move(place), _) => {
                            if place.local == current {
                                queue.push_back(dest);
                                seen.insert(dest);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        if !reaches_ret {
            continue;
        }

        // For indirect wrappers: remap inner call args to outer callee args.
        if let Some(effect) = inner_effect {
            match effect {
                CallEffect::ReturnPointerAdd {
                    base_arg: inner_base,
                    offset_arg: inner_offset,
                    stride,
                }
                | CallEffect::ReturnPointerSub {
                    base_arg: inner_base,
                    offset_arg: inner_offset,
                    stride,
                } => {
                    let base_arg = trace_to_callee_arg(tcx, body, &args.get(inner_base)?.node)?;
                    let offset_arg = trace_to_callee_arg(tcx, body, &args.get(inner_offset)?.node)?;
                    return Some(match effect {
                        CallEffect::ReturnPointerSub { .. } => CallEffect::ReturnPointerSub {
                            base_arg,
                            offset_arg,
                            stride,
                        },
                        _ => CallEffect::ReturnPointerAdd {
                            base_arg,
                            offset_arg,
                            stride,
                        },
                    });
                }
                _ => {}
            }
            continue;
        }

        // Map inner call args to callee argument indices by tracing back
        // through Copy/Move assignments to the callee's parameter locals.
        let base_arg = trace_to_callee_arg(tcx, body, &args[0].node)?;
        let offset_arg = trace_to_callee_arg(tcx, body, &args[1].node)?;
        // Use the inner call's destination to compute the byte stride,
        // not the wrapper's return type (which may differ after a cast).
        let stride = if primitive.is_some_and(PrimitiveCall::is_byte_pointer_arithmetic) {
            Some(1)
        } else {
            destination_stride(tcx, callee, Some(call_dest.local))
        };

        return if is_sub {
            Some(CallEffect::ReturnPointerSub {
                base_arg,
                offset_arg,
                stride,
            })
        } else {
            Some(CallEffect::ReturnPointerAdd {
                base_arg,
                offset_arg,
                stride,
            })
        };
    }

    None
}

/// Use the existing dataflow graph to approximate local callee return deps.
fn local_return_dependencies(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    callee.as_local()?;
    if !tcx.is_mir_available(callee) {
        return None;
    }
    catch_unwind(AssertUnwindSafe(|| {
        let mut analyzer = DataflowAnalyzer::new(tcx, false);
        analyzer.build_graph(callee);
        let deps = analyzer.get_fn_arg2ret(callee);
        deps.iter_enumerated()
            .filter_map(|(local, depends)| {
                if *depends && local.as_usize() > 0 {
                    Some(local.as_usize() - 1)
                } else {
                    None
                }
            })
            .collect()
    }))
    .ok()
}

/// Return callee argument indices that are definitely written on every
/// reachable return path.
fn local_must_write_args(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    callee.as_local()?;
    if !tcx.is_mir_available(callee) {
        return None;
    }

    catch_unwind(AssertUnwindSafe(|| {
        let body = tcx.optimized_mir(callee);
        let mut graph = PathGraph::new(tcx, callee);
        graph.find_scc();
        let mut enumerator = PathEnumerator::new(&graph);
        let paths = enumerator.enumerate_paths_repeat(0);

        let mut must_write: Option<HashSet<usize>> = None;
        for path in paths.iter() {
            if !path_ends_in_return(body, &path) {
                continue;
            }
            let writes = write_args_on_path(tcx, body, &path);
            must_write = Some(match must_write {
                Some(current) => current.intersection(&writes).copied().collect(),
                None => writes,
            });
        }

        must_write
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>()
    }))
    .ok()
}

/// Recognize `core::slice::range` (re-exported as `slice::range`), whose result
/// `Range { start, end }` satisfies `0 <= start <= end <= bounds.end`.
fn is_slice_range_fn(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    base.ends_with("slice::range") || base.contains("slice::index::range")
}

/// Recognize the standard-library `get_disjoint_check_valid` helper as a
/// trusted index-disjoint validator by name.
///
/// Its body validates indices through the `GetDisjointMutIndex` trait methods
/// `is_in_bounds(len)` and `is_overlapping(other)` rather than through literal
/// element loads and comparisons, so the structural detector cannot recognize
/// it.  The signature is `get_disjoint_check_valid(indices: &[I; N], len: usize)`,
/// hence `indices_arg = 0` and `len_arg = 1`.
fn named_index_disjoint_validator(name: &str) -> Option<(usize, usize)> {
    let base = name
        .split('<')
        .next()
        .unwrap_or(name)
        .trim_end_matches("::");
    if base.ends_with("get_disjoint_check_valid") {
        Some((0, 1))
    } else {
        None
    }
}

fn is_align_to_offsets_fn(name: &str) -> bool {
    name.contains("::align_to_offsets")
}

/// Detect an "index disjoint validator": a function whose body loads elements
/// from an array argument, and returns early (`Err`) both when an element is
/// out of range against a scalar argument (`>= len`) and when two elements are
/// equal (a duplicate).  Returns `(indices_arg, len_arg)`.
///
/// This is a *trusted* structural interprocedural summary, in the same spirit
/// as the name-based std-primitive summaries: the validator's loop coverage is
/// not re-proved here.  It only fires when the body literally contains both an
/// element-vs-scalar range comparison and an element-vs-element equality
/// comparison over the same array argument.
fn detect_index_disjoint_validator(tcx: TyCtxt<'_>, callee: DefId) -> Option<(usize, usize)> {
    use rustc_middle::mir::{BinOp, ProjectionElem};
    callee.as_local()?;
    if !tcx.is_mir_available(callee) {
        return None;
    }
    catch_unwind(AssertUnwindSafe(|| {
        let body = tcx.optimized_mir(callee);
        let arg_count = body.arg_count;
        let mut elem_load_arg: HashSet<(Local, usize)> = HashSet::new();
        let mut copy_of_arg: HashSet<(Local, usize)> = HashSet::new();

        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if !dest.projection.is_empty() {
                    continue;
                }
                let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rvalue else {
                    continue;
                };
                let Some(arg) = arg_of_local(place.local, arg_count) else {
                    continue;
                };
                if place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Index(_)))
                {
                    elem_load_arg.insert((dest.local, arg));
                } else if place.projection.is_empty() {
                    copy_of_arg.insert((dest.local, arg));
                }
            }
        }

        let elem_arg = |op: &Operand<'_>| -> Option<usize> {
            let (Operand::Copy(p) | Operand::Move(p)) = op else {
                return None;
            };
            if !p.projection.is_empty() {
                return None;
            }
            elem_load_arg
                .iter()
                .find(|(l, _)| *l == p.local)
                .map(|(_, a)| *a)
        };
        let scalar_arg = |op: &Operand<'_>| -> Option<usize> {
            let (Operand::Copy(p) | Operand::Move(p)) = op else {
                return None;
            };
            if !p.projection.is_empty() {
                return None;
            }
            arg_of_local(p.local, arg_count).or_else(|| {
                copy_of_arg
                    .iter()
                    .find(|(l, _)| *l == p.local)
                    .map(|(_, a)| *a)
            })
        };

        let mut bounds: Option<(usize, usize)> = None;
        let mut disjoint_arg: Option<usize> = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (_, Rvalue::BinaryOp(op, pair)) = &**assign else {
                    continue;
                };
                let (a, b) = &**pair;
                match op {
                    BinOp::Ge | BinOp::Gt | BinOp::Le | BinOp::Lt => {
                        if let (Some(idx), Some(len)) = (elem_arg(a), scalar_arg(b)) {
                            bounds = Some((idx, len));
                        } else if let (Some(idx), Some(len)) = (elem_arg(b), scalar_arg(a)) {
                            bounds = Some((idx, len));
                        }
                    }
                    BinOp::Eq | BinOp::Ne => {
                        if let (Some(x), Some(y)) = (elem_arg(a), elem_arg(b))
                            && x == y
                        {
                            disjoint_arg = Some(x);
                        }
                    }
                    _ => {}
                }
            }
        }

        match (bounds, disjoint_arg) {
            (Some((idx, len)), Some(dj)) if dj == idx && idx != len => Some((idx, len)),
            _ => None,
        }
    }))
    .ok()
    .flatten()
}

/// Return the zero-based argument index of `local`, if it is a MIR argument.
fn arg_of_local(local: Local, arg_count: usize) -> Option<usize> {
    let i = local.as_usize();
    if i >= 1 && i <= arg_count {
        Some(i - 1)
    } else {
        None
    }
}

fn path_ends_in_return(body: &rustc_middle::mir::Body<'_>, path: &[usize]) -> bool {
    path.last().is_some_and(|block| {
        body.basic_blocks
            .get(BasicBlock::from_usize(*block))
            .and_then(|data| data.terminator.as_ref())
            .is_some_and(|terminator| matches!(terminator.kind, TerminatorKind::Return))
    })
}

fn write_args_on_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    path: &[usize],
) -> HashSet<usize> {
    let mut writes = HashSet::new();
    for block in path {
        let Some(data) = body.basic_blocks.get(BasicBlock::from_usize(*block)) else {
            continue;
        };
        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        let name = call_name(tcx, func);
        if PrimitiveCall::classify(&name) != Some(PrimitiveCall::PtrWrite) {
            continue;
        }
        if let Some(pointer_arg) = args
            .first()
            .and_then(|arg| trace_to_callee_arg(tcx, body, &arg.node))
        {
            writes.insert(pointer_arg);
        }
    }
    writes
}

/// Return the byte stride for a pointer returned into `destination`.
fn destination_stride<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Option<Local>,
) -> Option<u64> {
    let destination = destination?;
    let ty = tcx.optimized_mir(caller).local_decls[destination].ty;
    let pointee = pointee_ty(ty)?;
    type_layout(tcx, caller, pointee).map(|(_, size)| size)
}

/// Return pointee alignment for a pointer returned into `destination`.
fn destination_pointee_alignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Option<Local>,
) -> Option<(u64, String)> {
    let destination = destination?;
    let ty = tcx.optimized_mir(caller).local_decls[destination].ty;
    let pointee = pointee_ty(ty).or(Some(ty))?;
    if let Some((align, _)) = type_layout(tcx, caller, pointee) {
        return Some((align, format!("{pointee:?}")));
    }
    if let TyKind::Array(elem, _) = pointee.kind()
        && let Some((align, _)) = type_layout(tcx, caller, *elem)
    {
        return Some((align, format!("{pointee:?}")));
    }
    Some((0, format!("{pointee:?}")))
}

/// Return pointee alignment when the destination is `NonNull<T>`.
fn destination_nonnull_alignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Option<Local>,
) -> Option<(u64, String)> {
    let destination = destination?;
    let ty = tcx.optimized_mir(caller).local_decls[destination].ty;
    let pointee = nonnull_inner_ty(tcx, ty)?;
    type_layout(tcx, caller, pointee).map(|(align, _)| (align, format!("{pointee:?}")))
}

fn is_nonnull_destination<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Option<Local>,
) -> bool {
    let Some(destination) = destination else {
        return false;
    };
    let ty = tcx.optimized_mir(caller).local_decls[destination].ty;
    nonnull_inner_ty(tcx, ty).is_some() || format!("{ty:?}").contains("NonNull<")
}

/// Return the pointee type of raw pointers and references.
fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

fn nonnull_inner_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let TyKind::Adt(def, args) = ty.kind() else {
        return None;
    };
    let path = tcx.def_path_str(def.did());
    if !path.contains("ptr::non_null::NonNull") {
        return None;
    }
    args.iter().find_map(|arg| match arg.kind() {
        GenericArgKind::Type(ty) => Some(ty),
        _ => None,
    })
}

fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if ty_has_param_const(ty) {
        return None;
    }
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, caller);
    let input = PseudoCanonicalInput {
        typing_env,
        value: ty,
    };
    match tcx.layout_of(input) {
        Ok(layout) => Some((layout.align.abi.bytes(), layout.size.bytes())),
        Err(_) if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
        Err(_) => None,
    }
}

fn ty_has_param_const(ty: Ty<'_>) -> bool {
    for arg in ty.walk() {
        match arg.kind() {
            GenericArgKind::Const(c) if matches!(c.kind(), ConstKind::Param(_)) => return true,
            GenericArgKind::Type(inner_ty) if matches!(inner_ty.kind(), TyKind::Alias(..)) => {
                return true;
            }
            _ => {}
        }
    }
    false
}
