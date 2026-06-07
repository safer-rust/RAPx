use crate::graphs::{
    cfg::{CfgBlock, ControlFlowGraph},
    scc::{Scc, SccInfo},
    scc_paths::{
        SccEnumeratedPath, SccPathAction, SccPathSemantics, SccPathTraversalConfig,
        SccPathTraversalState, WholeCfgPathEnumerator, compute_path_sensitive_paths,
        enumerate_scc_paths_cached,
    },
};
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::{
    mir::{BasicBlock, Rvalue, StatementKind, TerminatorKind, UnwindAction},
    ty::TyCtxt,
};
use rustc_span::def_id::DefId;

#[derive(Clone)]
pub struct PathGraph<'tcx> {
    pub cfg: ControlFlowGraph<'tcx>,
}

struct PathSccPathSemantics<'a, 'tcx> {
    graph: &'a mut PathGraph<'tcx>,
}

impl<'a, 'tcx> SccPathSemantics for PathSccPathSemantics<'a, 'tcx> {
    fn enumerate_child_paths(
        &mut self,
        child_enter: usize,
        constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        let child_scc = self.graph.cfg.block(child_enter).scc.clone();
        self.graph.find_scc_paths(child_enter, &child_scc, constraints)
    }

    fn enumerate_actions(
        &mut self,
        _scc: &SccInfo,
        state: &SccPathTraversalState,
        constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccPathAction> {
        let mut actions = vec![SccPathAction::RecordExit {
            constraints: constraints.clone(),
        }];
        for next in self.graph.cfg.block(state.cur).next.clone() {
            actions.push(SccPathAction::Traverse {
                next,
                constraints: constraints.clone(),
            });
        }
        actions
    }
}

impl<'tcx> PathGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> PathGraph<'tcx> {
        let body = tcx.optimized_mir(def_id);
        let basicblocks = &body.basic_blocks;
        let mut cfg_blocks = Vec::<CfgBlock<'tcx>>::new();
        let mut discriminants = FxHashMap::default();

        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cfg_block = CfgBlock::new(i, bb.is_cleanup);

            for stmt in &bb.statements {
                if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
                    cfg_block.assigned_locals.insert(place.local.as_usize());
                    if let Rvalue::Discriminant(rv_place) = rvalue {
                        discriminants.insert(place.local.as_usize(), rv_place.local.as_usize());
                    }
                }
            }

            let Some(terminator) = &bb.terminator else {
                continue;
            };
            cfg_block.terminator = Some(terminator.clone());

            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target } => {
                    cfg_block.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    for (_, ref target) in targets.iter() {
                        cfg_block.add_next(target.as_usize());
                    }
                    cfg_block.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref target,
                    ref unwind,
                    ..
                } => {
                    if let Some(tt) = target {
                        cfg_block.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cfg_block.add_next(tt.as_usize());
                    }
                }
                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cfg_block.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::InlineAsm {
                    template: _,
                    operands: _,
                    options: _,
                    line_spans: _,
                    ref unwind,
                    targets,
                    asm_macro: _,
                } => {
                    for target in targets {
                        cfg_block.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                _ => {}
            }

            cfg_blocks.push(cfg_block);
        }

        let mut cfg = ControlFlowGraph::new(def_id, tcx, cfg_blocks);
        cfg.discriminants = discriminants;

        PathGraph { cfg }
    }

    pub fn find_scc(&mut self) {
        self.cfg.find_scc();
    }

    pub fn get_path_sensitive_paths(&mut self) -> Vec<Vec<usize>> {
        compute_path_sensitive_paths(self)
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.cfg.sort_scc_tree(scc)
    }

    pub fn find_scc_paths(
        &mut self,
        start: usize,
        scc: &SccInfo,
        initial_constraints: &FxHashMap<usize, usize>,
    ) -> Vec<SccEnumeratedPath> {
        let def_id = self.cfg.def_id;
        let mut semantics = PathSccPathSemantics { graph: self };
        enumerate_scc_paths_cached(
            def_id,
            start,
            scc,
            initial_constraints.clone(),
            &mut semantics,
            SccPathTraversalConfig::default(),
        )
    }
}

impl<'tcx> WholeCfgPathEnumerator for PathGraph<'tcx> {
    fn block_count(&self) -> usize {
        self.cfg.blocks.len()
    }

    fn block_nexts(&self, index: usize) -> Vec<usize> {
        self.cfg.block(index).next.iter().copied().collect()
    }

    fn block_scc_enter(&self, index: usize) -> usize {
        self.cfg.block(index).scc.enter
    }

    fn block_has_scc_members(&self, index: usize) -> bool {
        !self.cfg.block(index).scc.nodes.is_empty()
    }

    fn enumerate_scc_paths_at(&mut self, enter: usize) -> Vec<SccEnumeratedPath> {
        let cur_scc = self.cfg.block(enter).scc.clone();
        let scc = self.sort_scc_tree(&cur_scc);
        self.find_scc_paths(enter, &scc, &FxHashMap::default())
    }
}
