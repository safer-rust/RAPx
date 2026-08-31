use super::MopFnAliasPairs;
use crate::{
    analysis::path::{
        PathTree,
        graph::{PathEnumerator, PathGraph},
    },
    analysis::points_to::graph::PtsGraph,
    compat::FxHashMap,
    graphs::cfg::CfgBlock,
    utils::source::get_fn_name,
};
use rustc_middle::mir::Terminator;
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, def_id::DefId};
use std::fmt;

use super::value::Value;

pub struct AliasGraph<'tcx> {
    pub path_graph: PathGraph<'tcx>,
    pub visit_times: usize,

    /// Per-slot type info — kept for SafeDrop compatibility.
    /// Indexed by value index = PtsGraph slot index.
    pub values: Vec<Value>,

    /// New unified PtsGraph for both MoP alias and SafeDrop.
    pub pts_graph: PtsGraph,

    /// Tracks Move operand destinations → source value indices.
    /// Used by SafeDrop to propagate drop info through move chains.
    pub move_sources: FxHashMap<usize, usize>,

    pub ret_alias: MopFnAliasPairs,
    pub arg_size: usize,
    pub span: Span,
}

impl<'tcx> AliasGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> AliasGraph<'tcx> {
        let fn_name = get_fn_name(tcx, def_id);
        rap_debug!("New an AliasGraph for: {:?}", fn_name);
        let path_graph = PathGraph::new(tcx, def_id);
        Self::from_path_graph(tcx, def_id, path_graph)
    }

    pub fn from_path_graph(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        path_graph: PathGraph<'tcx>,
    ) -> AliasGraph<'tcx> {
        let body = tcx.optimized_mir(def_id);
        let locals = &body.local_decls;
        let arg_size = body.arg_count;
        let mut values = Vec::<Value>::new();
        for local in locals.indices() {
            let node = Value::new(local.as_usize(), local.as_usize());
            values.push(node);
        }
        AliasGraph {
            path_graph,
            visit_times: 0,
            values,
            pts_graph: PtsGraph::new(),
            move_sources: FxHashMap::default(),
            ret_alias: MopFnAliasPairs::new(arg_size),
            arg_size,
            span: body.span,
        }
    }

    pub fn def_id(&self) -> DefId {
        self.path_graph.def_id()
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.path_graph.tcx()
    }

    pub fn arg_size(&self) -> usize {
        self.arg_size
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock {
        self.path_graph.cfg_block(index)
    }

    pub fn terminator(&self, index: usize) -> Option<&Terminator<'tcx>> {
        self.path_graph.terminator(index)
    }

    pub fn enumerate_paths(&self) -> PathTree {
        let mut enumerator = PathEnumerator::new(&self.path_graph);
        enumerator.enumerate_paths()
    }

    pub fn visit_times(&self) -> usize {
        self.visit_times
    }

    pub fn increment_visit_times(&mut self) -> usize {
        self.visit_times += 1;
        self.visit_times
    }

    // ── Index translation: value index → PtsGraph slot index ──

    pub fn value_to_slot_idx(&self, value_idx: usize) -> Option<usize> {
        self.values.get(value_idx).and_then(|v| v.slot_idx)
    }

    pub fn get_alias_set(&self, e: usize) -> Option<Vec<usize>> {
        let e_slot = self.value_to_slot_idx(e)?;
        let mut result = vec![e];
        for i in 0..self.values.len() {
            if i == e {
                continue;
            }
            if let Some(i_slot) = self.value_to_slot_idx(i) {
                if self.pts_graph.may_alias(e_slot, i_slot) {
                    result.push(i);
                }
            }
        }
        if result.len() > 1 { Some(result) } else { None }
    }

    // ── Value type queries (delegate to PtsGraph) ──

    pub fn value_may_drop(&self, value_idx: usize) -> bool {
        self.value_to_slot_idx(value_idx)
            .map(|s| self.pts_graph.may_drop(s))
            .unwrap_or(false)
    }

    pub fn value_is_ptr(&self, value_idx: usize) -> bool {
        self.value_to_slot_idx(value_idx)
            .map(|si| self.pts_graph.slot_is_ptr(si))
            .unwrap_or(false)
    }
}

impl<'tcx> std::fmt::Display for AliasGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "AliasGraph {{")?;
        writeln!(f, "  def_id: {:?}", self.def_id())?;
        writeln!(f, "  values: {:?}", self.values)?;
        writeln!(f, "  cfg_blocks: {:?}", self.path_graph.cfg.blocks)?;
        writeln!(f, "  disc_info: {:?}", self.path_graph.disc_info)?;
        write!(f, "}}")
    }
}
