//! VM-backed leak checks for allocations whose ownership is intentionally
//! converted to a raw pointer or reference.

use crate::analysis::path::default::PathAnalyzer;
use crate::compat::{FxHashMap, FxHashSet};
use crate::def_ids::{diagnostic_api, type_ids};
use crate::helpers::mir_scan::collect_global_local_pairs;
use crate::helpers::mir_utils::resolve_callee_def_id;
use crate::vm::{RelevantItem, VmExecutor, constructor_policy::ConstructorMirMode, state::AllocId};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Location, Operand, Place, StatementKind, TerminatorKind,
        visit::{NonUseContext, PlaceContext, Visitor},
    },
    ty::{IntTy, Ty, TyCtxt, TyKind, UintTy},
};
use rustc_span::Span;
use z3::ast::Ast;
use z3::{Config, Context};

struct LeakPath<'z3, 'tcx> {
    vm: VmExecutor<'z3, 'tcx>,
    raw_allocs: FxHashMap<AllocId, Span>,
    constant_format_args: FxHashSet<Local>,
}

/// Find owned allocations released into raw pointers on completed, supported paths.
pub(super) fn detect(tcx: TyCtxt<'_>) -> FxHashMap<DefId, Vec<Span>> {
    let functions: Vec<_> = tcx
        .mir_keys(())
        .iter()
        .map(|local| local.to_def_id())
        .filter(|&def_id| {
            if !matches!(
                tcx.def_kind(def_id),
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure
            ) || !tcx.is_mir_available(def_id)
            {
                return false;
            }
            let body = tcx.optimized_mir(def_id);
            body.basic_blocks
                .iter()
                .any(|block| is_ownership_release_call(tcx, body, &block.terminator().kind))
        })
        .collect();
    if functions.is_empty() {
        return FxHashMap::default();
    }
    let mut paths = PathAnalyzer::new(tcx, false);
    let config = Config::new();
    let context = Context::new(&config);
    let mut leaked = FxHashMap::default();
    for def_id in functions {
        let Some(tree) = paths.analyze(def_id) else {
            continue;
        };
        if tree.is_truncated() || !tcx.is_mir_available(def_id) {
            continue;
        }
        let body = tcx.optimized_mir(def_id);
        let output = body.local_decls[Local::from_usize(0)].ty;
        if !return_cannot_carry_pointer(output) || !external_places_are_unrelated(tcx, def_id, body)
        {
            continue;
        }
        let mut spans = Vec::new();
        for path in tree.to_vecs() {
            let Some(&last) = path.last() else { continue };
            if !matches!(
                body.basic_blocks[BasicBlock::from_usize(last)]
                    .terminator()
                    .kind,
                TerminatorKind::Return
            ) {
                continue;
            }
            // Constructor MIR distinguishes an empty Vec from a real heap buffer.
            let vm = VmExecutor::new(&context, tcx, def_id, None, ConstructorMirMode::True);
            let mut states: Vec<_> = vm
                .execute_items(&[])
                .into_iter()
                .map(|vm| LeakPath {
                    vm,
                    raw_allocs: FxHashMap::default(),
                    constant_format_args: FxHashSet::default(),
                })
                .collect();
            for (position, &bb_idx) in path.iter().enumerate() {
                let block = BasicBlock::from_usize(bb_idx);
                for stmt_index in 0..body.basic_blocks[block].statements.len() {
                    states = execute(
                        states,
                        RelevantItem::Statement {
                            def_id,
                            block,
                            global_block: None,
                            stmt_index,
                        },
                        tcx,
                    );
                }
                states = execute(
                    states,
                    RelevantItem::Terminator {
                        def_id,
                        block,
                        global_block: None,
                        switch_succ: path.get(position + 1).copied().map(BasicBlock::from_usize),
                    },
                    tcx,
                );
            }
            for state in states
                .iter()
                .filter(|state| !state.vm.diagnostics().is_unsupported())
            {
                for (id, span) in &state.raw_allocs {
                    let facts = &state.vm.alloc(*id).facts;
                    if !facts.dead
                        && !facts.drop_may_free
                        && !facts.function_var_may_drop
                        && !spans.contains(span)
                    {
                        spans.push(*span);
                    }
                }
            }
        }
        if !spans.is_empty() {
            leaked.insert(def_id, spans);
        }
    }
    leaked
}

fn return_cannot_carry_pointer(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Tuple(fields) => fields.iter().all(return_cannot_carry_pointer),
        TyKind::Bool | TyKind::Char | TyKind::Int(..) | TyKind::Uint(..) | TyKind::Float(..) => {
            true
        }
        _ => false,
    }
}

/// Reject external places that could retain a released allocation.
fn external_places_are_unrelated<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
) -> bool {
    if collect_global_local_pairs(tcx, def_id)
        .keys()
        .any(|&static_id| {
            !matches!(
                tcx.type_of(static_id).instantiate_identity().skip_norm_wip().kind(),
                TyKind::Bool
                    | TyKind::Char
                    | TyKind::Int(IntTy::I8 | IntTy::I16 | IntTy::I32)
                    | TyKind::Uint(UintTy::U8 | UintTy::U16 | UintTy::U32)
                    | TyKind::Float(..)
            )
        })
    {
        return false;
    }
    struct ExternalPlaces {
        pointer_args: FxHashSet<Local>,
        unrelated: bool,
    }
    impl<'tcx> Visitor<'tcx> for ExternalPlaces {
        fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
            if self.pointer_args.contains(&place.local)
                && !matches!(context, PlaceContext::NonUse(NonUseContext::VarDebugInfo))
            {
                self.unrelated = false;
            }
            self.super_place(place, context, location);
        }
    }
    let mut visitor = ExternalPlaces {
        pointer_args: body
            .args_iter()
            .filter(|&local| {
                matches!(
                    body.local_decls[local].ty.kind(),
                    TyKind::RawPtr(..) | TyKind::Ref(..)
                )
            })
            .collect(),
        unrelated: true,
    };
    visitor.visit_body(body);
    visitor.unrelated
}

fn execute<'z3, 'tcx>(
    states: Vec<LeakPath<'z3, 'tcx>>,
    item: RelevantItem<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Vec<LeakPath<'z3, 'tcx>> {
    let mut next = Vec::new();
    for LeakPath {
        vm,
        raw_allocs,
        constant_format_args,
    } in states
    {
        let (raw_alloc, may_escape, irrelevant_call) = if let RelevantItem::Terminator {
            def_id,
            block,
            ..
        } = item
        {
            let terminator = vm.body_for(def_id).basic_blocks[block].terminator();
            if let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
                && is_ownership_release_call(tcx, vm.body(), &terminator.kind)
                && let Operand::Move(_) = &args[0].node
            {
                let value = vm.value_of_operand(&args[0].node);
                let source_alloc = value.provenance_alloc_id().or_else(|| {
                    let Operand::Move(place) = &args[0].node else {
                        return None;
                    };
                    let path = vm.container_ptr_field(value.ty)?;
                    vm.field_value(place.local, &path)?.provenance_alloc_id()
                });
                let allocation = source_alloc.and_then(|header| {
                    vm.container_data_alloc(header, value.ty)
                        .or_else(|| {
                            (vm.alloc(header).facts.owning.is_some() || is_std_owner_type(value.ty))
                                .then_some(header)
                        })
                        .filter(|id| {
                            vm.alloc(*id).facts.owning.is_some() || is_std_owner_type(value.ty)
                        })
                        .filter(|id| {
                            vm.alloc(*id).size.simplify().as_u64() != Some(0)
                                && vm
                                    .alloc(*id)
                                    .element_ty
                                    .as_ty()
                                    .is_none_or(|ty| vm.size_of_ty(ty) != 0)
                        })
                        .map(|id| (id, destination.local, terminator.source_info.span))
                });
                (allocation, allocation.is_none(), false)
            } else {
                let may_escape = !is_raw_pointer_discard(tcx, def_id, &terminator.kind, &vm)
                    && call_may_escape(&vm, &terminator.kind, &raw_allocs, &constant_format_args);
                let irrelevant_call = !raw_allocs.is_empty()
                    && !may_escape
                    && matches!(&terminator.kind, TerminatorKind::Call { destination, .. } if destination.ty(vm.body(), tcx).ty.is_unit());
                (None, may_escape, irrelevant_call)
            }
        } else {
            (None, false, false)
        };
        let mut constant_format_args = constant_format_args;
        match item {
            RelevantItem::Statement {
                def_id,
                block,
                stmt_index,
                ..
            } => {
                if let StatementKind::Assign(assign) =
                    &vm.body_for(def_id).basic_blocks[block].statements[stmt_index].kind
                {
                    constant_format_args.remove(&assign.0.local);
                }
            }
            RelevantItem::Terminator { def_id, block, .. } => {
                if let TerminatorKind::Call {
                    func, destination, ..
                } = &vm.body_for(def_id).basic_blocks[block].terminator().kind
                {
                    constant_format_args.remove(&destination.local);
                    if is_constant_format_constructor(tcx, def_id, func) {
                        constant_format_args.insert(destination.local);
                    }
                }
            }
            _ => {}
        }
        // A unit-returning call with no path to a tracked allocation cannot change its ownership.
        if irrelevant_call {
            next.push(LeakPath {
                vm,
                raw_allocs,
                constant_format_args,
            });
            continue;
        }
        for vm in VmExecutor::execute_items_after(vec![vm], std::slice::from_ref(&item)) {
            let mut raw_allocs = if may_escape {
                FxHashMap::default()
            } else {
                raw_allocs.clone()
            };
            if let Some((id, destination, span)) = raw_alloc
                && returned_allocation(&vm, destination, id)
            {
                raw_allocs.insert(id, span);
            }
            next.push(LeakPath {
                vm,
                raw_allocs,
                constant_format_args: constant_format_args.clone(),
            });
        }
    }
    next
}

fn call_may_escape<'z3, 'tcx>(
    vm: &VmExecutor<'z3, 'tcx>,
    term: &TerminatorKind<'tcx>,
    raw_allocs: &FxHashMap<AllocId, Span>,
    constant_format_args: &FxHashSet<Local>,
) -> bool {
    let (TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. }) = term else {
        return false;
    };
    args.iter().any(|arg| {
        // A constant cannot refer to a heap allocation created by this function.
        if matches!(arg.node, Operand::Constant(..)) { return false; }
        let value = vm.value_of_operand(&arg.node);
        match value.ty.kind() {
            TyKind::RawPtr(..) | TyKind::Ref(..) => value.provenance_alloc_id().is_none_or(|id| raw_allocs.contains_key(&id)),
            TyKind::Adt(..) | TyKind::Tuple(..) | TyKind::Array(..) => !matches!(&arg.node,
                Operand::Move(place) | Operand::Copy(place) if constant_format_args.contains(&place.local)),
            _ => false,
        }
    })
}

fn is_constant_format_constructor<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> bool {
    resolve_callee_def_id(tcx, caller, func).is_some_and(|callee| {
        matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
            && tcx.def_path_str(callee).contains("fmt::Arguments::")
            && matches!(tcx.item_name(callee).as_str(), "new_const" | "from_str")
    })
}

fn is_raw_pointer_discard<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    term: &TerminatorKind<'tcx>,
    vm: &VmExecutor<'_, 'tcx>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = term else {
        return false;
    };
    if args.len() != 1
        || !matches!(
            vm.value_of_operand(&args[0].node).ty.kind(),
            TyKind::RawPtr(..)
        )
    {
        return false;
    }
    resolve_callee_def_id(tcx, caller, func).is_some_and(|callee| {
        diagnostic_api::is_drop(tcx, callee)
            || (matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
                && tcx.def_path_str(callee).ends_with("::mem::forget"))
    })
}

fn is_std_owner_type(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Adt(adt, _) if type_ids::is_std_box(adt.did())
        || type_ids::is_std_vec(adt.did()) || type_ids::is_std_string(adt.did())
        || type_ids::is_std_cstring(adt.did()) || type_ids::is_std_rc(adt.did()))
}

fn is_ownership_release_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    term: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call {
        args, destination, ..
    } = term
    else {
        return false;
    };
    let output = destination.ty(body, tcx).ty;
    if !matches!(output.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))
        && !matches!(output.kind(), TyKind::Tuple(fields) if fields.iter().any(|field| matches!(field.kind(), TyKind::RawPtr(..) | TyKind::Ref(..))))
    {
        return false;
    }
    args.len() == 1
        && matches!(&args[0].node, Operand::Move(place) if matches!(place.ty(body, tcx).ty.kind(), TyKind::Adt(..)))
}

fn returned_allocation(vm: &VmExecutor<'_, '_>, destination: Local, id: AllocId) -> bool {
    if vm
        .local_value(destination)
        .and_then(|value| value.provenance_alloc_id())
        == Some(id)
    {
        return true;
    }
    let ty = vm.body().local_decls[destination].ty;
    matches!(ty.kind(), TyKind::Tuple(fields) if fields.iter().enumerate().any(|(index, _)| {
        vm.field_value(destination, &[index]).and_then(|value| value.provenance_alloc_id()) == Some(id)
    }))
}
