mod bug_records;
mod vm;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::Analysis;
use crate::analysis::path::default::PathAnalyzer;
use crate::utils::source::get_fn_name;

pub struct SafeDrop<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> SafeDrop<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
    pub fn start(&self) {
        let mut path_analyzer = PathAnalyzer::new(self.tcx, false);
        path_analyzer.run();
        rap_info!("================================");
        let mir_keys = self.tcx.mir_keys(());
        for local_def_id in mir_keys {
            query_safedrop(self.tcx, local_def_id.to_def_id(), &path_analyzer);
        }
    }
}

fn query_safedrop<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, path_analyzer: &PathAnalyzer<'tcx>) {
    let fn_name = get_fn_name(tcx, def_id);
    if fn_name
        .as_ref()
        .is_some_and(|s| s.contains("__raw_ptr_deref_dummy"))
    {
        return;
    }
    rap_trace!("query_safedrop: {:?}", fn_name);
    if let Some(_other) = tcx.hir_body_const_context(def_id.expect_local()) {
        return;
    }
    if tcx.is_mir_available(def_id) {
        if let Some(paths) = path_analyzer.get_fn_paths(def_id) {
            vm::analyze(tcx, def_id, &paths);
        }
    }
}
