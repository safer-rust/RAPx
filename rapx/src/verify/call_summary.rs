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
    mir::{Local, Operand},
    ty::{PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};

use crate::analysis::core::dataflow::{DataFlowAnalysis, default::DataFlowAnalyzer};

use super::backward_visit::ForgetReason;

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
    /// The return value is known to be non-zero.
    ReturnNonZero,
    /// The return value is known to satisfy a concrete alignment.
    ReturnAligned { align: u64, ty_name: String },
    /// The call reads memory through an argument.
    ReadMemory { arg: usize },
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

    if is_as_ptr_call(&name) || is_as_mut_ptr_call(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_pointer_add_call(&name) || is_pointer_offset_call(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0, 1],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_pointer_read_call(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_len_call(&name) {
        return CallDependencySummary {
            callee,
            name,
            return_depends_on_args: vec![0],
            may_write_args: Vec::new(),
            unsupported: false,
        };
    }

    if is_layout_constant_call(&name) {
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

    if is_as_ptr_call(&name) || is_as_mut_ptr_call(&name) {
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

    if is_pointer_add_call(&name) || is_pointer_offset_call(&name) {
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

    if is_pointer_read_call(&name) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReadMemory { arg: 0 }],
            unsupported: false,
        };
    }

    if is_len_call(&name) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: vec![CallEffect::ReturnLengthOfArg { arg: 0 }],
            unsupported: false,
        };
    }

    if is_layout_constant_call(&name) {
        return CallEffectSummary {
            callee,
            name,
            destination,
            effects: Vec::new(),
            unsupported: false,
        };
    }

    if let Some(callee) = callee {
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
    name.ends_with("::as_ptr") || name.contains("::as_ptr")
}

/// Return true for mutable pointer extraction calls.
pub fn is_as_mut_ptr_call(name: &str) -> bool {
    name.ends_with("::as_mut_ptr") || name.contains("::as_mut_ptr")
}

/// Return true for typed pointer addition calls.
pub fn is_pointer_add_call(name: &str) -> bool {
    name.contains("::add") || name.contains("::wrapping_add")
}

/// Return true for typed pointer offset calls.
pub fn is_pointer_offset_call(name: &str) -> bool {
    name.contains("::offset") || name.contains("::wrapping_offset")
}

/// Return true for pointer reads.
pub fn is_pointer_read_call(name: &str) -> bool {
    name.contains("::read") || name.ends_with("read")
}

/// Return true for slice/string/vector length queries.
pub fn is_len_call(name: &str) -> bool {
    name.ends_with("::len") || name.contains("::len")
}

/// Return true for layout constant producers.
pub fn is_layout_constant_call(name: &str) -> bool {
    name.contains("align_of") || name.contains("size_of")
}

/// Use the existing dataflow graph to approximate local callee return deps.
fn local_return_dependencies(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    callee.as_local()?;
    catch_unwind(AssertUnwindSafe(|| {
        let mut analyzer = DataFlowAnalyzer::new(tcx, false);
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
