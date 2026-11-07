use crate::analysis::path::PathTree;
use crate::check::safedrop::bug_records::{BugRecords, BugType, LocalSpot, TyBug};
use crate::compat::FxHashMap;
use crate::utils::source::{get_filename, get_name};
use crate::verify::slicer::RelevantItem;
use crate::verify::vm::VmState;
use crate::verify::vm::state::{AllocId, MemoryEvent, MemoryEventKind};
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{BasicBlock, Local, TerminatorKind}, ty::TyCtxt};
use rustc_span::Symbol;
use z3::{Config, Context};

pub(crate) fn analyze<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, paths: &PathTree) {
    let config = Config::new();
    let context = Context::new(&config);
    let body = tcx.optimized_mir(def_id);
    let mut bugs = BugRecords::new();
    for path in paths.to_vecs() {
        let mut state = VmState::new(&context, tcx, def_id, None);
        state.memory_events.enable();
        let mut states = state.execute_items(&[]);
        for (position, &bb_idx) in path.iter().enumerate() {
            let block = BasicBlock::from_usize(bb_idx);
            let data = &body.basic_blocks[block];
            for statement_index in 0..data.statements.len() {
                let item = RelevantItem::Statement {
                    def_id,
                    block,
                    global_block: None,
                    statement_index,
                };
                states = VmState::execute_items_after(states, &[item]);
            }
            let item = RelevantItem::Terminator {
                def_id,
                block,
                global_block: None,
                switch_succ: path.get(position + 1).copied().map(BasicBlock::from_usize),
            };
            states = VmState::execute_items_after(states, &[item]);
        }
        for state in &states {
            if state.path_infeasible {
                continue;
            }
            if let Some(&last) = path.last() {
                record_dangling_exit(state, body, last);
            }
            collect_events(&state.memory_events.events(), body, &mut bugs);
        }
    }
    report(tcx, def_id, body, &bugs);
}

fn record_dangling_exit<'z3, 'tcx>(
    state: &VmState<'z3, 'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    last: usize,
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
            state.memory_events.push(MemoryEvent {
                alloc_id,
                kind: MemoryEventKind::DanglingPointer,
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
    events: &[MemoryEvent],
    body: &rustc_middle::mir::Body<'tcx>,
    bugs: &mut BugRecords,
) {
    let mut drops: FxHashMap<AllocId, LocalSpot> = FxHashMap::default();
    for event in events {
        let Some(bb) = event.block else { continue };
        let is_cleanup = body.basic_blocks[BasicBlock::from_usize(bb)].is_cleanup;
        let trigger = LocalSpot::new(bb, event.local);
        match event.kind {
            MemoryEventKind::Drop => {
                drops.insert(event.alloc_id, trigger);
            }
            MemoryEventKind::DoubleFree
            | MemoryEventKind::UseAfterFree
            | MemoryEventKind::DanglingPointer => {
                let drop_spot = drops.get(&event.alloc_id).copied().unwrap_or_default();
                let (kind, map) = match event.kind {
                    MemoryEventKind::DoubleFree if is_cleanup => {
                        (BugType::DoubleFree, &mut bugs.df_bugs_unwind)
                    }
                    MemoryEventKind::DoubleFree => (BugType::DoubleFree, &mut bugs.df_bugs),
                    MemoryEventKind::UseAfterFree => (BugType::UseAfterFree, &mut bugs.uaf_bugs),
                    MemoryEventKind::DanglingPointer if is_cleanup => {
                        (BugType::DanglingPointer, &mut bugs.dp_bugs_unwind)
                    }
                    MemoryEventKind::DanglingPointer => {
                        (BugType::DanglingPointer, &mut bugs.dp_bugs)
                    }
                    MemoryEventKind::Drop => unreachable!(),
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
