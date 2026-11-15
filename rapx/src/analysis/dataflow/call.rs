//! MIR dataflow queries used to describe a callee at a call site.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand},
    ty::{Mutability, TyCtxt, TyKind},
};

use super::{
    call_write::{self, WriteSemantics},
    graph::build_dataflow_graph,
};
use crate::compat::Spanned;

/// Dependencies needed to retain a call during backward slicing.
#[derive(Clone, Debug)]
pub(crate) struct CallDependencies {
    /// Arguments that can affect the call's return value.
    pub return_depends_on_args: Vec<usize>,
    /// Arguments whose referents the call may write.
    pub write_args: Vec<usize>,
    /// Arguments needed to model those writes during backward slicing.
    pub write_inputs: Vec<usize>,
}

impl CallDependencies {
    pub(crate) fn fallback(arg_count: usize) -> Self {
        Self {
            return_depends_on_args: (0..arg_count).collect(),
            write_args: Vec::new(),
            write_inputs: Vec::new(),
        }
    }
}

/// Verification-specific call models supplement MIR-derived dependencies.
pub(crate) trait CallSemantics: WriteSemantics {
    fn special_dependencies<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        callee: DefId,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        body: &Body<'tcx>,
    ) -> Option<CallDependencies>;

    fn skip_mir_dependencies(&self, tcx: TyCtxt<'_>, callee: DefId) -> bool;
    fn preserve_all_return_args(&self, tcx: TyCtxt<'_>, callee: DefId) -> bool;
}

/// Combine MIR dataflow with the verifier's special call semantics.
pub(crate) fn dependencies<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    body: &Body<'tcx>,
    semantics: &impl CallSemantics,
) -> CallDependencies {
    let arg_count = args.len();
    let Some(callee) = crate::helpers::mir_utils::dep_callee_def_id(func) else {
        return CallDependencies::fallback(arg_count);
    };
    if let Some(summary) = semantics.special_dependencies(tcx, caller, callee, func, args, body) {
        return summary;
    }
    if semantics.skip_mir_dependencies(tcx, callee) {
        return CallDependencies::fallback(arg_count);
    }

    // The write and return dependencies are independent: a callee can write
    // through an argument while returning a value derived from another one.
    let write_args =
        call_write::callsite_write_args(semantics, tcx, caller, func).unwrap_or_else(|| {
            tcx.fn_sig(callee)
                .skip_binder()
                .inputs()
                .skip_binder()
                .iter()
                .enumerate()
                .filter_map(|(i, ty)| {
                    (i < arg_count
                        && matches!(
                            ty.kind(),
                            TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(_, Mutability::Mut)
                        ))
                    .then_some(i)
                })
                .collect()
        });
    let write_args: Vec<_> = write_args.into_iter().filter(|i| *i < arg_count).collect();
    let return_deps = if semantics.preserve_all_return_args(tcx, callee) {
        Some((0..arg_count).collect())
    } else {
        return_dependencies(tcx, callee)
    };
    if !write_args.is_empty() || return_deps.is_some() {
        return CallDependencies {
            return_depends_on_args: return_deps
                .map(|args| args.into_iter().filter(|i| *i < arg_count).collect())
                .unwrap_or_else(|| (0..arg_count).collect()),
            write_inputs: write_args.clone(),
            write_args,
        };
    }
    CallDependencies::fallback(arg_count)
}

/// Arguments that can flow into the return value of a callee with available MIR.
///
/// `None` means the graph could not be built; callers must retain all arguments
/// in that case. An empty vector means the return is independent of arguments.
pub(crate) fn return_dependencies(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    crate::helpers::mir_utils::catch_panic(|| {
        build_dataflow_graph(tcx, callee)
            .param_return_deps()
            .iter_enumerated()
            .filter_map(|(local, depends)| {
                (*depends && local.as_usize() > 0).then_some(local.as_usize() - 1)
            })
            .collect()
    })
    .ok()
}
