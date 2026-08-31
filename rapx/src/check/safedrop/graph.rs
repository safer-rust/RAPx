use super::{bug_records::*, drop::*};
use crate::analysis::{
    alias::default::graph::AliasGraph, heap_ownership::HeapOwnershipResultMap,
    path::graph::PathGraph,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use std::fmt;

/// We represent each target function with the `SafeDropGraph` struct and then perform analysis
/// based on the struct.
pub struct SafeDropGraph<'tcx> {
    pub alias_graph: AliasGraph<'tcx>,
    pub bug_records: BugRecords,
    pub drop_record: Vec<DropRecord>,
    // analysis of heap item
    pub adt_owner: HeapOwnershipResultMap,
}

impl<'tcx> SafeDropGraph<'tcx> {
    pub fn from_path_graph(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        path_graph: PathGraph<'tcx>,
        adt_owner: HeapOwnershipResultMap,
    ) -> Self {
        Self::from_alias_graph(
            AliasGraph::from_path_graph(tcx, def_id, path_graph),
            adt_owner,
        )
    }

    fn from_alias_graph(alias_graph: AliasGraph<'tcx>, adt_owner: HeapOwnershipResultMap) -> Self {
        let mut drop_record = Vec::<DropRecord>::new();
        for v in &alias_graph.values {
            drop_record.push(DropRecord::false_record(v.index));
        }
        SafeDropGraph {
            alias_graph,
            bug_records: BugRecords::new(),
            drop_record,
            adt_owner,
        }
    }
}

impl<'tcx> std::fmt::Display for SafeDropGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SafeDropGraph {{")?;
        writeln!(f, "  AliasGraph: {}", self.alias_graph)?;
        write!(f, "}}")
    }
}
