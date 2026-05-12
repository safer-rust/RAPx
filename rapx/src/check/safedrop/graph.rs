use super::{bug_records::*, drop::*};
use crate::analysis::core::{
    alias_analysis::default::graph::MopGraph, ownedheap_analysis::OHAResultMap,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use std::{fmt, vec::Vec};

/// We represent each target function with the `SafeDropGraph` struct and then perform analysis
/// based on the struct.
pub struct SafeDropGraph<'tcx> {
    pub mop_graph: MopGraph<'tcx>,
    pub bug_records: BugRecords,
    pub drop_record: Vec<DropRecord>,
    // analysis of heap item
    pub adt_owner: OHAResultMap,
}

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, adt_owner: OHAResultMap) -> Self {
        let mop_graph = MopGraph::new(tcx, def_id);
        let mut drop_record = Vec::<DropRecord>::new();
        for v in &mop_graph.values {
            drop_record.push(DropRecord::false_record(v.index));
        }

        SafeDropGraph {
            mop_graph,
            bug_records: BugRecords::new(),
            drop_record,
            adt_owner,
        }
    }
}

impl<'tcx> std::fmt::Display for SafeDropGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SafeDropGraph {{")?;
        writeln!(f, "  MopGraph: {}", self.mop_graph)?;
        write!(f, "}}")
    }
}
