pub mod debug;
pub mod default;
pub mod graph;

use std::{
    collections::{HashMap, HashSet},
    fmt::{self},
};

pub mod types;
use crate::{analysis::Analysis, utils::source::get_fn_name_byid};
pub use types::*;

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::Local;

pub type Graph = DataflowGraph;
pub type GraphNode = DataflowNode;
pub type GraphEdge = DataflowEdge;

pub type Arg2Ret = IndexVec<Local, bool>;
pub type Arg2RetMap = HashMap<DefId, IndexVec<Local, bool>>;
pub type DataflowGraphMap = HashMap<DefId, DataflowGraph>;

pub struct Arg2RetMapWrapper(pub Arg2RetMap);

/// This trait provides features related to dataflow analysis.
pub trait DataflowAnalysis: Analysis {
    fn get_fn_dataflow(&self, def_id: DefId) -> Option<DataflowGraph>;
    fn get_all_dataflow(&self) -> DataflowGraphMap;
    fn has_flow_between(&self, def_id: DefId, local1: Local, local2: Local) -> bool;
    fn collect_equivalent_locals(&self, def_id: DefId, local: Local) -> HashSet<Local>;
    fn get_fn_arg2ret(&self, def_id: DefId) -> Arg2Ret;
    fn get_all_arg2ret(&self) -> Arg2RetMap;
}

impl fmt::Display for Arg2RetMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print dataflow analysis results ===")?;
        for (def_id, arg2ret) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Function: {:?}", fn_name)?;
            for (local, depends) in arg2ret.iter_enumerated() {
                if local.as_u32() > 0 && *depends {
                    writeln!(f, "  Argument {:?} ---> Return value _0", local)?;
                }
            }
        }
        Ok(())
    }
}
