use crate::analysis::path::PathTree;
use crate::check::safedrop::bug_records::{BugRecords, BugType, LocalSpot, TyBug};
use crate::compat::FxHashMap;
use crate::def_ids::type_ids;
use crate::verify::config::ConstructorMirMode;
use crate::utils::source::{get_filename, get_name};
use crate::verify::{AllocId, Diagnostics, MemoryEvent, MemoryEventKind, RelevantItem, ValueFacts, VmExecutor, VmValue};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{BasicBlock, Local, TerminatorKind}, ty::{TyCtxt, TyKind}};
use rustc_span::{Span, Symbol};
use std::cell::RefCell;
use z3::{Config, Context};

#[derive(Clone, Copy)]
enum SafeDropEventKind {
    Drop,
    DoubleFree,
    UseAfterFree,
    DanglingPointer,
}

struct SafeDropEvent {
    alloc_id: AllocId,
    kind: SafeDropEventKind,
    block: Option<usize>,
    local: usize,
    span: Span,
}

fn classify_event(event: &MemoryEvent) -> Option<SafeDropEvent> {
    let kind = match (event.kind, event.was_dead) {
        (MemoryEventKind::Drop, false) => SafeDropEventKind::Drop,
        (MemoryEventKind::Drop, true) => SafeDropEventKind::DoubleFree,
        (MemoryEventKind::Use, true) => SafeDropEventKind::UseAfterFree,
        (MemoryEventKind::Use, false) => return None,
    };
    Some(SafeDropEvent {
        alloc_id: event.alloc_id,
        kind,
        block: event.block,
        local: event.local,
        span: event.span,
    })
}

/// Execute one MIR item and recover only the opaque calls SafeDrop can safely continue past.
fn execute_item<'z3, 'tcx>(states: Vec<VmExecutor<'z3, 'tcx>>, item: &RelevantItem<'tcx>) -> Vec<VmExecutor<'z3, 'tcx>> {
    let mut next = Vec::new();
    for state in states {
        let recovery = if let RelevantItem::Terminator { def_id, block, .. } = item {
            let terminator = state.body_for(*def_id).basic_blocks[*block].terminator();
            if let TerminatorKind::Call { args, destination, .. } = &terminator.kind {
                let scalar_args = args.iter().all(|arg| {
                    let value = state.value_of_operand(&arg.node);
                    value.provenance.is_none() && !matches!(value.ty.kind(), TyKind::Ref(..) | TyKind::RawPtr(..))
                });
                Some((state.path_state.diagnostics.clone(), destination.local, scalar_args))
            } else {
                None
            }
        } else {
            None
        };
        for mut state in VmExecutor::execute_items_after_with_cleanup(vec![state], std::slice::from_ref(item)) {
            if let Some((before, destination, scalar_args)) = &recovery {
                recover_opaque_call(&mut state, before, *destination, *scalar_args);
            }
            next.push(state);
        }
    }
    next
}

fn recover_opaque_call<'z3, 'tcx>(state: &mut VmExecutor<'z3, 'tcx>, before: &Diagnostics, destination: Local, scalar_args: bool) {
    let ty = state.body().local_decls[destination].ty;
    if state.path_state.diagnostics.only_copy_memory_target_unavailable_since(before)
        && matches!(ty.kind(), TyKind::Adt(def, _) if type_ids::is_std_string(def.did()))
    {
        let mut facts = ValueFacts::default();
        if state.init_box_vec_param(destination, ty, destination.as_usize(), &mut facts) {
            state.path_state.diagnostics.recover_copy_memory_target(before);
        }
    } else if scalar_args && state.path_state.diagnostics.only_missing_mir_since(before) {
        let mut facts = ValueFacts::default();
        if !state.init_box_vec_param(destination, ty, destination.as_usize(), &mut facts) {
            state.set_local(destination, VmValue::new(state.fresh_int("opaque_result"), ty));
        }
        state.path_state.diagnostics.recover_missing_mir(before);
    }
}

pub(crate) fn analyze<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, paths: &PathTree) {
    let config = Config::new();
    let context = Context::new(&config);
    let body = tcx.optimized_mir(def_id);
    let mut bugs = BugRecords::new();
    for path in paths.to_vecs() {
        let mut state = VmExecutor::new(&context, tcx, def_id, None, ConstructorMirMode::Default);
        state.path_state.memory_events = Some(RefCell::default());
        let mut states = state.execute_items(&[]);
        for (position, &bb_idx) in path.iter().enumerate() {
            let block = BasicBlock::from_usize(bb_idx);
            let data = &body.basic_blocks[block];
            for stmt_index in 0..data.statements.len() {
                let item = RelevantItem::Statement {
                    def_id,
                    block,
                    global_block: None,
                    stmt_index,
                };
                states = execute_item(states, &item);
            }
            let item = RelevantItem::Terminator {
                def_id,
                block,
                global_block: None,
                switch_succ: path.get(position + 1).copied().map(BasicBlock::from_usize),
            };
            states = execute_item(states, &item);
        }
        for state in &states {
            let trace = state.path_state.memory_events.as_ref().expect("memory trace enabled");
            let mut events: Vec<_> = trace.borrow().iter().filter_map(classify_event).collect();
            if let Some(&last) = path.last() {
                record_dangling_exit(state, body, last, &mut events);
            }
            collect_events(&events, body, &mut bugs);
        }
    }
    report(tcx, def_id, body, &bugs);
}

fn record_dangling_exit<'z3, 'tcx>(
    state: &VmExecutor<'z3, 'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    last: usize,
    events: &mut Vec<SafeDropEvent>,
) {
    let data = &body.basic_blocks[BasicBlock::from_usize(last)];
    let is_cleanup = data.is_cleanup;
    let is_return = matches!(data.terminator().kind, TerminatorKind::Return);
    if !is_cleanup && !is_return {
        return;
    }
    for local_idx in (if is_cleanup { 1 } else { 0 })..=body.arg_count {
        let local = Local::from_usize(local_idx);
        if local_idx > 0
            && !matches!(
                body.local_decls[local].ty.kind(),
                rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
            )
        {
            continue;
        }
        if let Some(alloc_id) = state
            .local_value(local)
            .and_then(|v| v.provenance_alloc_id())
            && state.alloc(alloc_id).facts.dead
        {
            events.push(SafeDropEvent {
                alloc_id,
                kind: SafeDropEventKind::DanglingPointer,
                block: Some(last),
                local: local_idx,
                span: if local_idx == 0 {
                    data.terminator().source_info.span
                } else {
                    body.span
                },
            });
        }
    }
}

fn collect_events<'tcx>(
    events: &[SafeDropEvent],
    body: &rustc_middle::mir::Body<'tcx>,
    bugs: &mut BugRecords,
) {
    let mut drops: FxHashMap<AllocId, LocalSpot> = FxHashMap::default();
    for event in events {
        let Some(bb) = event.block else { continue };
        let is_cleanup = body.basic_blocks[BasicBlock::from_usize(bb)].is_cleanup;
        let trigger = LocalSpot::new(bb, event.local);
        match event.kind {
            SafeDropEventKind::Drop => {
                drops.insert(event.alloc_id, trigger);
            }
            SafeDropEventKind::DoubleFree
            | SafeDropEventKind::UseAfterFree
            | SafeDropEventKind::DanglingPointer => {
                let drop_spot = drops.get(&event.alloc_id).copied().unwrap_or_default();
                let (kind, map) = match event.kind {
                    SafeDropEventKind::DoubleFree if is_cleanup => {
                        (BugType::DoubleFree, &mut bugs.df_bugs_unwind)
                    }
                    SafeDropEventKind::DoubleFree => (BugType::DoubleFree, &mut bugs.df_bugs),
                    SafeDropEventKind::UseAfterFree => (BugType::UseAfterFree, &mut bugs.uaf_bugs),
                    SafeDropEventKind::DanglingPointer if is_cleanup => {
                        (BugType::DanglingPointer, &mut bugs.dp_bugs_unwind)
                    }
                    SafeDropEventKind::DanglingPointer => {
                        (BugType::DanglingPointer, &mut bugs.dp_bugs)
                    }
                    SafeDropEventKind::Drop => unreachable!(),
                };
                map.entry(event.local).or_insert(TyBug {
                    drop_spot,
                    trigger_info: trigger,
                    span: event.span,
                    confidence: 99,
                    bug_type: kind,
                });
            }
        }
    }
}

fn report<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &rustc_middle::mir::Body<'tcx>,
    bugs: &BugRecords,
) {
    if bugs.is_bug_free() || get_filename(tcx, def_id).is_some_and(|name| name.contains(".cargo")) {
        return;
    }
    let name = get_name(tcx, def_id).unwrap_or_else(|| Symbol::intern("no symbol available"));
    let span = tcx.def_span(def_id);
    bugs.df_bugs_output(body, name, span);
    bugs.uaf_bugs_output(body, name, span);
    bugs.dp_bug_output(body, name, span);
}
