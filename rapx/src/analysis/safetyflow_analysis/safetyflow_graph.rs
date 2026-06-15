use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Write},
};

use crate::{helpers::fn_info::*, utils::source::get_adt_name};
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::ty::TyCtxt;

use super::safetyflow_unit::SafetyFlowUnit;
use petgraph::{
    Graph,
    dot::{Config, Dot},
    graph::{DiGraph, EdgeReference, NodeIndex},
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum SafetyFlowNode {
    SafeFn(DefId),
    UnsafeFn(DefId),
    MergedCallerCons(Vec<DefId>),
    MutMethods(Vec<DefId>),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum SafetyFlowEdge {
    CallerToCallee,
    ConsToMethod,
    MutToCaller,
}

impl SafetyFlowNode {
    pub fn from(node: FnInfo) -> Self {
        match node.fn_safety {
            Safety::Unsafe => SafetyFlowNode::UnsafeFn(node.def_id),
            Safety::Safe => SafetyFlowNode::SafeFn(node.def_id),
        }
    }
}

impl fmt::Display for SafetyFlowNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SafetyFlowNode::SafeFn(_) => write!(f, "Safe"),
            SafetyFlowNode::UnsafeFn(_) => write!(f, "Unsafe"),
            SafetyFlowNode::MergedCallerCons(_) => write!(f, "MergedCallerCons"),
            SafetyFlowNode::MutMethods(_) => write!(f, "MutMethods"),
        }
    }
}

impl fmt::Display for SafetyFlowEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SafetyFlowEdge::CallerToCallee => write!(f, "CallerToCallee"),
            SafetyFlowEdge::ConsToMethod => write!(f, "ConsToMethod"),
            SafetyFlowEdge::MutToCaller => write!(f, "MutToCaller"),
        }
    }
}

fn shape_for_fn_kind(kind: FnKind) -> &'static str {
    match kind {
        FnKind::Constructor => "septagon",
        FnKind::Method => "ellipse",
        _ => "box",
    }
}

fn def_ids_to_label(tcx: TyCtxt<'_>, def_ids: &[DefId]) -> String {
    def_ids
        .iter()
        .map(|did| tcx.def_path_str(*did))
        .collect::<Vec<_>>()
        .join("\\n")
}

/// Holds graph data for a single module before DOT generation.
pub struct SafetyFlowGraph {
    structs: HashMap<String, HashSet<FnInfo>>,
    edges: HashSet<(DefId, DefId, SafetyFlowEdge)>,
    nodes: HashMap<DefId, String>,
}

impl SafetyFlowGraph {
    pub fn new() -> Self {
        Self {
            structs: HashMap::new(),
            edges: HashSet::new(),
            nodes: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, tcx: TyCtxt<'_>, node: FnInfo, custom_label: Option<String>) {
        let adt_name = get_adt_name(tcx, node.def_id);
        self.structs.entry(adt_name).or_default().insert(node);

        if !self.nodes.contains_key(&node.def_id) || custom_label.is_some() {
            let attr = if let Some(label) = custom_label {
                let shape = shape_for_fn_kind(node.fn_kind);
                format!(
                    "label=\"{}\", shape=\"{}\", style=\"filled\", fillcolor=\"#f0f0f0\", color=\"#555555\"",
                    label, shape
                )
            } else {
                let sf_node = SafetyFlowNode::from(node);
                Self::node_to_dot_attr(tcx, &sf_node, node.fn_kind)
            };

            self.nodes.insert(node.def_id, attr);
        }
    }

    pub fn add_edge(&mut self, from: DefId, to: DefId, edge_type: SafetyFlowEdge) {
        if from == to {
            return;
        }
        self.edges.insert((from, to, edge_type));
    }

    pub fn to_dot(&self, module_name: &str) -> String {
        let mut dot = String::new();
        let graph_id = module_name
            .replace("::", "_")
            .replace(|c: char| !c.is_alphanumeric(), "_");

        writeln!(dot, "digraph {} {{", graph_id).unwrap();
        writeln!(dot, "    compound=true;").unwrap();
        writeln!(dot, "    rankdir=LR;").unwrap();

        for (struct_name, nodes) in &self.structs {
            let cluster_id = format!(
                "cluster_{}",
                struct_name.replace(|c: char| !c.is_alphanumeric(), "_")
            );

            writeln!(dot, "    subgraph {} {{", cluster_id).unwrap();
            writeln!(dot, "        label=\"{}\";", struct_name).unwrap();
            writeln!(dot, "        style=dashed;").unwrap();
            writeln!(dot, "        color=gray;").unwrap();

            for node in nodes {
                let def_id = node.def_id;
                let node_id =
                    format!("n_{:?}", def_id).replace(|c: char| !c.is_alphanumeric(), "_");

                if let Some(attr) = self.nodes.get(&def_id) {
                    writeln!(dot, "        {} [{}];", node_id, attr).unwrap();
                }
            }
            writeln!(dot, "    }}").unwrap();
        }

        for (from, to, edge_type) in &self.edges {
            let from_id = format!("n_{:?}", from).replace(|c: char| !c.is_alphanumeric(), "_");
            let to_id = format!("n_{:?}", to).replace(|c: char| !c.is_alphanumeric(), "_");

            let attr = match edge_type {
                SafetyFlowEdge::CallerToCallee => "color=black, style=solid",
                SafetyFlowEdge::ConsToMethod => "color=black, style=dotted",
                SafetyFlowEdge::MutToCaller => "color=blue, style=dashed",
            };

            writeln!(dot, "    {} -> {} [{}];", from_id, to_id, attr).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    fn node_to_dot_attr(tcx: TyCtxt<'_>, node: &SafetyFlowNode, kind: FnKind) -> String {
        let shape = shape_for_fn_kind(kind);
        match node {
            SafetyFlowNode::SafeFn(def_id) => {
                let label = tcx.def_path_str(*def_id);
                format!("label=\"{}\", color=black, shape=\"{}\"", label, shape)
            }
            SafetyFlowNode::UnsafeFn(def_id) => {
                let label = tcx.def_path_str(*def_id);
                format!("label=\"{}\", shape=\"{}\", color=red", label, shape)
            }
            _ => "label=\"Unknown\"".to_string(),
        }
    }

    pub fn generate_dot_from_unit(tcx: TyCtxt<'_>, unit: &SafetyFlowUnit) -> String {
        let mut graph: Graph<SafetyFlowNode, SafetyFlowEdge> = DiGraph::new();

        let get_edge_attr =
            |_graph: &Graph<SafetyFlowNode, SafetyFlowEdge>,
             edge_ref: EdgeReference<'_, SafetyFlowEdge>| {
                match edge_ref.weight() {
                    SafetyFlowEdge::CallerToCallee => "color=black, style=solid",
                    SafetyFlowEdge::ConsToMethod => "color=black, style=dotted",
                    SafetyFlowEdge::MutToCaller => "color=blue, style=dashed",
                }
                .to_owned()
            };

        let get_node_attr = |_graph: &Graph<SafetyFlowNode, SafetyFlowEdge>,
                             node_ref: (NodeIndex, &SafetyFlowNode)| {
            match node_ref.1 {
                SafetyFlowNode::SafeFn(def_id) => {
                    let label = tcx.def_path_str(*def_id);
                    format!(
                        "label=\"{}\", color=black, shape=\"{}\"",
                        label,
                        shape_for_fn_kind(unit.caller.fn_kind)
                    )
                }
                SafetyFlowNode::UnsafeFn(def_id) => {
                    let label = tcx.def_path_str(*def_id);
                    format!("label=\"{}\\n \", shape=\"box\", color=red", label)
                }
                SafetyFlowNode::MergedCallerCons(def_ids) => {
                    let label = def_ids_to_label(tcx, def_ids);
                    format!(
                        "label=\"Caller Constructors\\n{}\", shape=box, style=filled, fillcolor=lightgrey",
                        label
                    )
                }
                SafetyFlowNode::MutMethods(def_ids) => {
                    let label = def_ids_to_label(tcx, def_ids);
                    format!(
                        "label=\"Mutable Methods\\n{}\", shape=octagon, style=filled, fillcolor=lightyellow",
                        label
                    )
                }
            }
        };

        let caller_node = graph.add_node(SafetyFlowNode::from(unit.caller));
        if !unit.caller_cons.is_empty() {
            let cons_def_ids: Vec<DefId> = unit.caller_cons.iter().map(|con| con.def_id).collect();
            let merged_cons_node = graph.add_node(SafetyFlowNode::MergedCallerCons(cons_def_ids));
            graph.add_edge(merged_cons_node, caller_node, SafetyFlowEdge::ConsToMethod);
        }

        if !unit.mut_methods.is_empty() {
            let def_ids: Vec<DefId> = unit.mut_methods.iter().copied().collect();
            let mut_methods_node = graph.add_node(SafetyFlowNode::MutMethods(def_ids));
            graph.add_edge(mut_methods_node, caller_node, SafetyFlowEdge::MutToCaller);
        }

        let mut dot_str = String::new();
        let dot = Dot::with_attr_getters(
            &graph,
            &[Config::NodeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );

        write!(dot_str, "{}", dot).unwrap();
        dot_str
    }
}
