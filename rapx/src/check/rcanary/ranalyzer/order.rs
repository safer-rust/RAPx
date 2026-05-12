use rustc_middle::{mir::TerminatorKind, ty::InstanceKind::Item};

use std::collections::BinaryHeap;
//use stopwatch::Stopwatch;

use super::super::RcxMut;
use super::super::ranalyzer::{FlowAnalysis, NodeOrder};

impl<'tcx, 'a> FlowAnalysis<'tcx, 'a> {
    pub fn order(&mut self) {
        // Get the Global TyCtxt from rustc
        // Grasp all mir Keys defined in current crate

        //let mut sw = Stopwatch::start_new();

        let tcx = self.tcx();
        let mir_keys = tcx.mir_keys(());

        for each_mir in mir_keys {
            // Get the defid of current crate and get mir Body through this id
            let def_id = each_mir.to_def_id();
            let body = tcx.instance_mir(Item(def_id));

            let mut path = NodeOrder::new(body);
            let mut lev: Vec<usize> = vec![0; body.basic_blocks.len()];

            path.collect_edges(&mut lev);
            path.topo_order(&mut lev);
            self.rcx_mut()
                .mir_graph_mut()
                .insert(def_id, path.graph_mut().clone());
        }
    }
}

impl<'tcx> NodeOrder<'tcx> {
    /// !Note: this function does not collect the edges that belongs to unwind paths.
    pub(crate) fn collect_edges(&mut self, lev: &mut Vec<usize>) {
        let bbs = &self.body().basic_blocks;
        for (block, data) in bbs.iter().enumerate() {
            let mut result: Vec<usize> = vec![];
            match &data.terminator().kind {
                TerminatorKind::Goto { target } => result.push(target.as_usize()),
                TerminatorKind::SwitchInt { targets, .. } => {
                    for bb in targets.all_targets() {
                        result.push(bb.as_usize());
                    }
                }
                TerminatorKind::Return => (),
                TerminatorKind::Unreachable => (),
                TerminatorKind::Drop { target, .. } => result.push(target.as_usize()),
                TerminatorKind::Assert { target, .. } => result.push(target.as_usize()),
                TerminatorKind::Yield { .. } => (),
                TerminatorKind::FalseEdge { .. } => (),
                TerminatorKind::FalseUnwind { .. } => (),
                TerminatorKind::InlineAsm { .. } => (),
                TerminatorKind::UnwindResume => (),
                TerminatorKind::UnwindTerminate(..) => (),
                TerminatorKind::CoroutineDrop => (),
                TerminatorKind::Call { target, .. } => {
                    // We check the destination due to following case.
                    // Terminator { source_info: SourceInfo { span: src/main.rs:100:9: 100:35 (#7), scope: scope[0] },
                    // kind: core::panicking::panic(const "assertion failed: index <= self.len") -> bb24 },
                    // destination -> None, cleanup -> Some(bb24)
                    match target {
                        Some(t) => result.push(t.as_usize()),
                        None => (),
                    }
                }
                TerminatorKind::TailCall { .. } => todo!(),
            }
            // Update the lev for generating topo order.
            for index in result.iter() {
                lev[*index] = lev[*index] + 1;
                self.graph_mut().get_pre_mut()[*index].push(block);
            }
            self.graph_mut().get_edges_mut()[block] = result;
        }
    }

    pub(crate) fn topo_order(&mut self, lev: &mut Vec<usize>) {
        let mut q: BinaryHeap<usize> = BinaryHeap::new();
        q.push(0);
        while !q.is_empty() {
            let top = q.pop().unwrap();
            self.graph_mut().get_topo_mut().push(top);
            for cnt in 0..self.graph().e[top].len() {
                let next = self.graph().e[top][cnt];
                lev[next] = lev[next] - 1;
                if lev[next] == 0 {
                    q.push(next);
                }
            }
        }
    }
}
