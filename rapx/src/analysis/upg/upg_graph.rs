use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Write},
};

use crate::{analysis::utils::fn_info::*, utils::source::get_adt_name};
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::ty::TyCtxt;

use super::upg_unit::UPGUnit;
use petgraph::{
    Graph,
    dot::{Config, Dot},
    graph::{DiGraph, EdgeReference, NodeIndex},
};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum UPGNode {
    SafeFn(DefId, String),
    UnsafeFn(DefId, String),
    MergedCallerCons(String),
    MutMethods(String),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum UPGEdge {
    CallerToCallee,
    ConsToMethod,
    MutToCaller,
}

impl UPGNode {
    pub fn from(node: FnInfo) -> Self {
        match node.fn_safety {
            Safety::Unsafe => match node.fn_kind {
                FnKind::Constructor => UPGNode::UnsafeFn(node.def_id, "box".to_string()),
                FnKind::Method => UPGNode::UnsafeFn(node.def_id, "ellipse".to_string()),
                FnKind::Fn => UPGNode::UnsafeFn(node.def_id, "box".to_string()),
                FnKind::Intrinsic => UPGNode::UnsafeFn(node.def_id, "box".to_string()),
            },
            Safety::Safe => match node.fn_kind {
                FnKind::Constructor => UPGNode::SafeFn(node.def_id, "box".to_string()),
                FnKind::Method => UPGNode::SafeFn(node.def_id, "ellipse".to_string()),
                FnKind::Fn => UPGNode::SafeFn(node.def_id, "box".to_string()),
                FnKind::Intrinsic => UPGNode::SafeFn(node.def_id, "box".to_string()),
            },
        }
    }
}

impl fmt::Display for UPGNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UPGNode::SafeFn(_, _) => write!(f, "Safe"),
            UPGNode::UnsafeFn(_, _) => write!(f, "Unsafe"),
            UPGNode::MergedCallerCons(_) => write!(f, "MergedCallerCons"),
            UPGNode::MutMethods(_) => write!(f, "MutMethods"),
        }
    }
}

impl fmt::Display for UPGEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UPGEdge::CallerToCallee => write!(f, "CallerToCallee"),
            UPGEdge::ConsToMethod => write!(f, "ConsToMethod"),
            UPGEdge::MutToCaller => write!(f, "MutToCaller"),
        }
    }
}

/// Holds graph data for a single module before DOT generation.
pub struct UPGraph {
    // Nodes grouped by their associated struct/type name.
    structs: HashMap<String, HashSet<FnInfo>>,
    // Edges between DefIds with their type.
    edges: HashSet<(DefId, DefId, UPGEdge)>,
    // Pre-generated DOT attribute strings for each node (DefId).
    nodes: HashMap<DefId, String>,
}

impl UPGraph {
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
                if node.fn_kind == FnKind::Constructor {
                    format!(
                        "label=\"{}\", shape=\"septagon\", style=\"filled\", fillcolor=\"#f0f0f0\", color=\"#555555\"",
                        label
                    )
                } else {
                    format!(
                        "label=\"{}\", shape=\"ellipse\", style=\"filled\", fillcolor=\"#f0f0f0\", color=\"#555555\"",
                        label
                    )
                }
            } else {
                let upg_node = UPGNode::from(node);
                Self::node_to_dot_attr(&upg_node)
            };

            self.nodes.insert(node.def_id, attr);
        }
    }

    pub fn add_edge(&mut self, from: DefId, to: DefId, edge_type: UPGEdge) {
        if from == to {
            return;
        }
        self.edges.insert((from, to, edge_type));
    }

    pub fn upg_unit_string(&self, module_name: &str) -> String {
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
                UPGEdge::CallerToCallee => "color=black, style=solid",
                UPGEdge::ConsToMethod => "color=black, style=dotted",
                UPGEdge::MutToCaller => "color=blue, style=dashed",
            };

            writeln!(dot, "    {} -> {} [{}];", from_id, to_id, attr).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }

    fn node_to_dot_attr(node: &UPGNode) -> String {
        match node {
            UPGNode::SafeFn(def_id, shape) => {
                format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
            }
            UPGNode::UnsafeFn(def_id, shape) => {
                let label = format!("{:?}", def_id);
                format!("label=\"{}\", shape={:?}, color=red", label, shape)
            }
            _ => "label=\"Unknown\"".to_string(),
        }
    }

    pub fn generate_dot_from_upg_unit(upg: &UPGUnit) -> String {
        let mut graph: Graph<UPGNode, UPGEdge> = DiGraph::new();
        let get_edge_attr = |_graph: &Graph<UPGNode, UPGEdge>,
                             edge_ref: EdgeReference<'_, UPGEdge>| {
            match edge_ref.weight() {
                UPGEdge::CallerToCallee => "color=black, style=solid",
                UPGEdge::ConsToMethod => "color=black, style=dotted",
                UPGEdge::MutToCaller => "color=blue, style=dashed",
            }
            .to_owned()
        };
        let get_node_attr =
            |_graph: &Graph<UPGNode, UPGEdge>, node_ref: (NodeIndex, &UPGNode)| match node_ref.1 {
                UPGNode::SafeFn(def_id, shape) => {
                    format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
                }
                UPGNode::UnsafeFn(def_id, shape) => {
                    let label = format!("{:?}\n ", def_id);
                    let node_attr = format!("label={:?}, shape={:?}, color=red", label, shape);
                    node_attr
                }
                UPGNode::MergedCallerCons(label) => {
                    format!(
                        "label=\"{}\", shape=box, style=filled, fillcolor=lightgrey",
                        label
                    )
                }
                UPGNode::MutMethods(label) => {
                    format!(
                        "label=\"{}\", shape=octagon, style=filled, fillcolor=lightyellow",
                        label
                    )
                }
            };

        let caller_node = graph.add_node(UPGNode::from(upg.caller));
        if !upg.caller_cons.is_empty() {
            let cons_labels: Vec<String> = upg
                .caller_cons
                .iter()
                .map(|con| format!("{:?}", con.def_id))
                .collect();
            let merged_label = format!("Caller Constructors\n{}", cons_labels.join("\n"));
            let merged_cons_node = graph.add_node(UPGNode::MergedCallerCons(merged_label));
            graph.add_edge(merged_cons_node, caller_node, UPGEdge::ConsToMethod);
        }

        if !upg.mut_methods.is_empty() {
            let mut_method_labels: Vec<String> = upg
                .mut_methods
                .iter()
                .map(|def_id| format!("{:?}", def_id))
                .collect();
            let merged_label = format!("Mutable Methods\n{}", mut_method_labels.join("\n"));

            let mut_methods_node = graph.add_node(UPGNode::MutMethods(merged_label));
            graph.add_edge(mut_methods_node, caller_node, UPGEdge::MutToCaller);
        }

        /*
        for (callee, cons) in &self.callee_cons_pair {
            let callee_node = graph.add_node(Self::get_node(*callee));
            for callee_cons in cons {
                let callee_cons_node = graph.add_node(Self::get_node(*callee_cons));
                graph.add_edge(callee_cons_node, callee_node, UPGEdge::ConsToMethod);
            }
            graph.add_edge(caller_node, callee_node, UPGEdge::CallerToCallee);
        }
        */
        let mut dot_str = String::new();
        let dot = Dot::with_attr_getters(
            &graph,
            // &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &[Config::NodeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );

        write!(dot_str, "{}", dot).unwrap();
        // println!("{}", dot_str);
        dot_str
    }

    pub fn nodes_def_ids(&self) -> Vec<DefId> {
        self.nodes.keys().map(|def_id| *def_id).collect()
    }
}
