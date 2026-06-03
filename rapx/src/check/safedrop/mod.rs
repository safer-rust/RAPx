pub mod alias;
pub mod bug_records;
pub mod corner_case;
pub mod drop;
pub mod graph;
pub mod safedrop;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::{
    analysis::core::{
        alias_analysis::default::{AliasAnalyzer, MopFnAliasMap},
        ownedheap_analysis::{OHAResultMap, OwnedHeapAnalysis, default::OwnedHeapAnalyzer},
    },
    graphs::scc::Scc,
    utils::source::get_fn_name,
};
use graph::SafeDropGraph;
use safedrop::*;

use crate::analysis::Analysis;

pub struct SafeDrop<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> SafeDrop<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
    pub fn start(&self) {
        let mut mop = AliasAnalyzer::new(self.tcx);
        mop.run();
        let fn_map = mop.get_all_fn_alias_raw();
        rap_info!("================================");
        rap_info!("Aliases found: {:?}", fn_map);

        let mut heap = OwnedHeapAnalyzer::new(self.tcx);
        heap.run();
        let adt_owner = heap.get_all_items();

        let mir_keys = self.tcx.mir_keys(());
        for local_def_id in mir_keys {
            query_safedrop(
                self.tcx,
                &fn_map,
                local_def_id.to_def_id(),
                adt_owner.clone(),
            );
        }
    }
}

pub fn query_safedrop(tcx: TyCtxt, fn_map: &MopFnAliasMap, def_id: DefId, adt_owner: OHAResultMap) {
    let fn_name = get_fn_name(tcx, def_id);
    if fn_name
        .as_ref()
        .map_or(false, |s| s.contains("__raw_ptr_deref_dummy"))
    {
        return;
    }
    rap_trace!("query_safedrop: {:?}", fn_name);
    /* filter const mir */

    /* filter const mir */
    if let Some(_other) = tcx.hir_body_const_context(def_id.expect_local()) {
        return;
    }
    if tcx.is_mir_available(def_id) {
        let mut safedrop_graph = SafeDropGraph::new(tcx, def_id, adt_owner);
        rap_debug!("safedrop grah (raw): {}", safedrop_graph);
        safedrop_graph.mop_graph.find_scc();
        rap_debug!("safedrop graph (scc): {}", safedrop_graph);
        safedrop_graph.check(0, fn_map);
        if safedrop_graph.mop_graph.visit_times <= VISIT_LIMIT {
            safedrop_graph.report_bugs();
        }
    }
}
