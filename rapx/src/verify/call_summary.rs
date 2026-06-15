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

use std::panic::{AssertUnwindSafe, catch_unwind};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};

use super::{path_refine::ForgetReason, primitive::PrimitiveCall};

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

    if primitive.is_some_and(PrimitiveCall::is_layout_constant) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: Vec::new(),
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if let Some(callee) = callee {
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

    if primitive.is_some_and(PrimitiveCall::is_pointer_add_like) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnPointerAdd {
                base_arg: 0,
                offset_arg: 1,
                stride: destination_stride(tcx, caller, destination),
            }],
            unsupported: false,
        };
    }

    if primitive.is_some_and(PrimitiveCall::is_pointer_sub_like) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnPointerSub {
                base_arg: 0,
                offset_arg: 1,
                stride: destination_stride(tcx, caller, destination),
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

    if let Some(callee) = callee {
        if let Some(effect) = try_pointer_arith_wrapper_effect(tcx, callee, destination) {
            return CallEffectSummary {
                callee: Some(callee),
                name,
                destination,
                effects: vec![effect],
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
    PrimitiveCall::classify(name) == Some(PrimitiveCall::PtrAdd)
}

/// Return true for typed pointer subtraction calls.
pub fn is_pointer_sub_call(name: &str) -> bool {
    PrimitiveCall::classify(name) == Some(PrimitiveCall::PtrSub)
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
    args.iter().find_map(|arg| arg.as_type())
}

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast
/// assignments to the outer callee's argument local, returning its index.
fn trace_to_callee_arg<'tcx>(
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
                    Rvalue::Use(Operand::Copy(place))
                    | Rvalue::Use(Operand::Move(place))
                    | Rvalue::Cast(_, Operand::Copy(place), _)
                    | Rvalue::Cast(_, Operand::Move(place), _) => place.local,
                    _ => continue,
                };
                if !seen.contains(&source) {
                    seen.insert(source);
                    queue.push_back(source);
                }
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

    let body = tcx.optimized_mir(callee);
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
                        Rvalue::Use(Operand::Copy(place)) | Rvalue::Use(Operand::Move(place)) => {
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
                    let base_arg = trace_to_callee_arg(body, &args.get(inner_base)?.node)?;
                    let offset_arg = trace_to_callee_arg(body, &args.get(inner_offset)?.node)?;
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
        let map_arg = |operand: &Operand<'_>| -> Option<usize> {
            let local = match operand {
                Operand::Copy(place) | Operand::Move(place) => place.local,
                _ => return None,
            };
            // Direct: the operand is already a callee parameter.
            let idx = local.as_usize();
            if idx >= 1 && idx <= body.arg_count {
                return Some(idx - 1);
            }
            // Indirect: trace back through assignments.
            let mut queue = VecDeque::from([local]);
            let mut seen = HashSet::from([local]);
            while let Some(current) = queue.pop_front() {
                let cidx = current.as_usize();
                if cidx >= 1 && cidx <= body.arg_count {
                    return Some(cidx - 1);
                }
                for bb2 in body.basic_blocks.iter() {
                    for stmt in &bb2.statements {
                        let StatementKind::Assign(assign) = &stmt.kind else {
                            continue;
                        };
                        let dest = assign.0.local;
                        if dest != current {
                            continue;
                        }
                        let source = match &assign.1 {
                            Rvalue::Use(Operand::Copy(place))
                            | Rvalue::Use(Operand::Move(place))
                            | Rvalue::Cast(_, Operand::Copy(place), _)
                            | Rvalue::Cast(_, Operand::Move(place), _) => place.local,
                            _ => continue,
                        };
                        if !seen.contains(&source) {
                            seen.insert(source);
                            queue.push_back(source);
                        }
                    }
                }
            }
            None
        };

        let base_arg = map_arg(&args[0].node)?;
        let offset_arg = map_arg(&args[1].node)?;
        // Use the inner call's destination to compute the byte stride,
        // not the wrapper's return type (which may differ after a cast).
        let stride = destination_stride(tcx, callee, Some(call_dest.local));

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
    type_layout(tcx, caller, pointee).map(|(align, _)| (align, format!("{pointee:?}")))
}

/// Return the pointee type of raw pointers and references.
fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

/// Return ABI alignment and size for a type in the caller environment.
fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, caller);
    let input = PseudoCanonicalInput {
        typing_env,
        value: ty,
    };
    let layout = tcx.layout_of(input).ok()?;
    Some((layout.align.abi.bytes(), layout.size.bytes()))
}
