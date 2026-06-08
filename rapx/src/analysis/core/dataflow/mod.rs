pub mod debug;
pub mod default;
pub mod graph;

use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Debug, Display},
};

use crate::{
    analysis::Analysis,
    utils::source::get_fn_name_byid,
};
pub use crate::graphs::dataflow::*;

impl From<DataflowGraph> for DataFlowGraph {
    fn from(graph: DataflowGraph) -> Self {
        let param_ret_deps = graph.param_return_deps();
        DataFlowGraph {
            nodes: graph.nodes,
            edges: graph.edges,
            param_ret_deps,
        }
    }
}

// Backward-compatible aliases for code migrating from old `Graph`/`GraphNode`/`GraphEdge` names.
pub type Graph = DataflowGraph;
pub type GraphNode = DataflowNode;
pub type GraphEdge = DataflowEdge;

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{mir::Local, ty::TyCtxt};

pub type Arg2Ret = IndexVec<Local, bool>;
pub type Arg2RetMap = HashMap<DefId, IndexVec<Local, bool>>;
#[derive(Clone)]
pub struct DataFlowGraph {
    pub nodes: GraphNodes,
    pub edges: GraphEdges,
    pub param_ret_deps: Arg2Ret,
}
pub type DataFlowGraphMap = HashMap<DefId, DataFlowGraph>;

pub struct Arg2RetWrapper(pub Arg2Ret);
pub struct Arg2RetMapWrapper(pub Arg2RetMap);
pub struct DataFlowGraphWrapper(pub DataFlowGraph);
pub struct DataFlowGraphMapWrapper(pub HashMap<DefId, DataFlowGraph>);

/// This trait provides features related to dataflow analysis.
pub trait DataFlowAnalysis: Analysis {
    fn get_fn_dataflow(&self, def_id: DefId) -> Option<DataFlowGraph>;
    fn get_all_dataflow(&self) -> DataFlowGraphMap;
    fn has_flow_between(&self, def_id: DefId, local1: Local, local2: Local) -> bool;
    fn collect_equivalent_locals(&self, def_id: DefId, local: Local) -> HashSet<Local>;
    fn get_fn_arg2ret(&self, def_id: DefId) -> Arg2Ret;
    fn get_all_arg2ret(&self) -> Arg2RetMap;
}

impl fmt::Display for Arg2RetWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let arg2ret: &Arg2Ret = &self.0;
        for (local, depends) in arg2ret.iter_enumerated() {
            if local.as_u32() > 0 {
                if *depends {
                    writeln!(f, "Argument {:?} ---> Return value _0", local)?;
                }
            }
        }
        Ok(())
    }
}

impl fmt::Display for Arg2RetMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print dataflow analysis results ===")?;
        for (def_id, arg2ret) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(
                f,
                "Function: {:?}\n{}",
                fn_name,
                Arg2RetWrapper(arg2ret.clone())
            )?;
        }
        Ok(())
    }
}

impl Display for DataFlowGraphWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let graph = &self.0;
        write!(
            f,
            "Graph statistics: {} nodes, {} edges.\n",
            graph.nodes.len(),
            graph.edges.len()
        )?;
        if graph.param_ret_deps.len() > 1 {
            write!(f, "Return value dependencies: \n")?;
        }
        for (node_idx, deps) in graph.param_ret_deps.iter_enumerated() {
            if node_idx.as_u32() > 0 {
                if *deps {
                    write!(f, "Argument {:?} ---> Return value _0.\n", node_idx)?;
                }
            }
        }

        for (node_idx, node) in graph.nodes.iter_enumerated() {
            let node_adj: Vec<Local> = node
                .out_edges
                .iter()
                .map(|edge_idx| graph.edges[*edge_idx].dst)
                .collect();
            if !node_adj.is_empty() {
                write!(f, "Node {:?} -> Node {:?}\n", node_idx, node_adj)?;
            }
        }
        Ok(())
    }
}

impl Debug for DataFlowGraphWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Nodes:")?;
        for node in &self.0.nodes {
            writeln!(f, "  {:?}", node)?;
        }
        writeln!(f, "Edges:")?;
        for edge in &self.0.edges {
            writeln!(f, "  {:?}", edge)?;
        }
        Ok(())
    }
}

impl Display for DataFlowGraphMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "===Print dataflow analysis resuts===")?;
        for (def_id, dfg) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(
                f,
                "Function: {:?}\n{}",
                fn_name,
                DataFlowGraphWrapper(dfg.clone())
            )?;
        }
        Ok(())
    }
}

impl Debug for DataFlowGraphMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (def_id, dfg) in &self.0 {
            writeln!(
                f,
                "DefId: {:?}\n{:?}",
                def_id,
                DataFlowGraphWrapper(dfg.clone())
            )?;
        }
        Ok(())
    }
}
