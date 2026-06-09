use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::Write;
use std::process::Command;

use crate::analysis::Analysis;
use crate::analysis::dataflow::*;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Local};
use rustc_middle::ty::TyCtxt;

pub struct DataFlowAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub graphs: HashMap<DefId, DataflowGraph>,
    pub debug: bool,
}

impl<'tcx> DataFlowAnalysis for DataFlowAnalyzer<'tcx> {
    fn get_fn_dataflow(&self, def_id: DefId) -> Option<DataFlowGraph> {
        self.graphs.get(&def_id).cloned().map(Into::into)
    }

    fn get_all_dataflow(&self) -> DataFlowGraphMap {
        self.graphs
            .iter()
            .map(|(&def_id, graph)| (def_id, graph.clone().into()))
            .collect()
    }

    fn has_flow_between(&self, def_id: DefId, local1: Local, local2: Local) -> bool {
        let graph = self.graphs.get(&def_id).unwrap();
        graph.is_connected(local1, local2)
    }

    fn collect_equivalent_locals(&self, def_id: DefId, local: Local) -> HashSet<Local> {
        let graph = self.graphs.get(&def_id).unwrap();
        graph.collect_equivalent_locals(local, true)
    }

    fn get_fn_arg2ret(&self, def_id: DefId) -> Arg2Ret {
        let graph = self.graphs.get(&def_id).unwrap();
        graph.param_return_deps()
    }

    fn get_all_arg2ret(&self) -> Arg2RetMap {
        let mut result = HashMap::new();
        for (def_id, graph) in &self.graphs {
            let deps = graph.param_return_deps();
            result.insert(*def_id, deps);
        }
        result
    }
}

impl<'tcx> Analysis for DataFlowAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "DataFlow Analysis"
    }

    fn run(&mut self) {
        self.build_graphs();
        if self.debug {
            self.draw_graphs();
        }
    }

    fn reset(&mut self) {
        self.graphs.clear();
    }
}

impl<'tcx> DataFlowAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self {
            tcx: tcx,
            graphs: HashMap::new(),
            debug,
        }
    }

    pub fn start(&mut self) {
        self.build_graphs();
        if self.debug {
            self.draw_graphs();
        }
    }

    pub fn build_graphs(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            let def_kind = self.tcx.def_kind(local_def_id);
            if matches!(def_kind, DefKind::Fn) || matches!(def_kind, DefKind::AssocFn) {
                if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                    let def_id = local_def_id.to_def_id();
                    self.build_graph(def_id);
                }
            }
        }
    }

    pub fn build_graph(&mut self, def_id: DefId) {
        if self.graphs.contains_key(&def_id) {
            return;
        }
        let body: &Body = self.tcx.optimized_mir(def_id);
        let mut graph =
            DataflowGraph::new(def_id, body.span, body.arg_count, body.local_decls.len());
        let basic_blocks = &body.basic_blocks;
        for basic_block_data in basic_blocks.iter() {
            for statement in basic_block_data.statements.iter() {
                graph.add_statm_to_graph(&statement);
            }
            if let Some(terminator) = &basic_block_data.terminator {
                graph.add_terminator_to_graph(&terminator);
            }
        }
        for closure_id in graph.closures.iter() {
            self.build_graph(*closure_id);
        }
        self.graphs.insert(def_id, graph);
    }

    pub fn draw_graphs(&self) {
        let dir_name = "DataflowGraph";

        Command::new("rm")
            .args(&["-rf", dir_name])
            .output()
            .expect("Failed to remove directory.");

        Command::new("mkdir")
            .args(&[dir_name])
            .output()
            .expect("Failed to create directory.");

        for (def_id, graph) in self.graphs.iter() {
            let name = self.tcx.def_path_str(def_id);
            let dot_file_name = format!("DataflowGraph/{}.dot", &name);
            let png_file_name = format!("DataflowGraph/{}.png", &name);
            let mut file = File::create(&dot_file_name).expect("Unable to create file.");
            let dot = graph.to_dot_graph(&self.tcx);
            file.write_all(dot.as_bytes())
                .expect("Unable to write data.");

            Command::new("dot")
                .args(&["-Tpng", &dot_file_name, "-o", &png_file_name])
                .output()
                .expect("Failed to execute Graphviz dot command.");
        }
    }
}
