pub mod alias;
pub mod graph;
pub mod mop;
pub mod stmt;
pub mod types;
pub mod value;

use super::{AliasAnalysis, AliasPair, FnAliasMap, FnAliasPairs};
use crate::compat::FxHashMap;
use crate::{
    analysis::{Analysis, path::default::PathAnalyzer},
    def_id::*,
    utils::source::*,
};
use graph::AliasGraph;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::{collections::HashSet, fmt};

pub const VISIT_LIMIT: usize = 80;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MopAliasPair {
    pub fact: AliasPair,
    pub lhs_may_drop: bool,
    pub lhs_need_drop: bool,
    pub rhs_may_drop: bool,
    pub rhs_need_drop: bool,
}

impl MopAliasPair {
    pub fn new(
        left_local: usize,
        lhs_may_drop: bool,
        lhs_need_drop: bool,
        right_local: usize,
        rhs_may_drop: bool,
        rhs_need_drop: bool,
    ) -> MopAliasPair {
        MopAliasPair {
            fact: AliasPair::new(left_local, right_local),
            lhs_may_drop,
            lhs_need_drop,
            rhs_may_drop,
            rhs_need_drop,
        }
    }

    pub fn swap(&mut self) {
        self.fact.swap();
        std::mem::swap(&mut self.lhs_may_drop, &mut self.rhs_may_drop);
        std::mem::swap(&mut self.lhs_need_drop, &mut self.rhs_need_drop);
    }

    pub fn left_local(&self) -> usize {
        self.fact.left_local
    }
    pub fn right_local(&self) -> usize {
        self.fact.right_local
    }
    pub fn lhs_fields(&self) -> &[usize] {
        &self.fact.lhs_fields
    }
    pub fn rhs_fields(&self) -> &[usize] {
        &self.fact.rhs_fields
    }
}

impl From<MopAliasPair> for AliasPair {
    fn from(m: MopAliasPair) -> Self {
        m.fact
    }
}

impl From<MopFnAliasPairs> for FnAliasPairs {
    fn from(m: MopFnAliasPairs) -> Self {
        FnAliasPairs {
            arg_size: m.arg_size,
            alias_set: m.alias_set.into_iter().map(Into::into).collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MopFnAliasPairs {
    pub arg_size: usize,
    pub alias_set: HashSet<MopAliasPair>,
}

impl fmt::Display for MopFnAliasPairs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.aliases()
                .iter()
                .map(|a| format!("{}", a.fact))
                .collect::<Vec<_>>()
                .join(",")
        )
    }
}

impl MopFnAliasPairs {
    pub fn new(arg_size: usize) -> Self {
        Self {
            arg_size,
            alias_set: HashSet::new(),
        }
    }
    pub fn arg_size(&self) -> usize {
        self.arg_size
    }
    pub fn aliases(&self) -> &HashSet<MopAliasPair> {
        &self.alias_set
    }
    pub fn add_alias(&mut self, alias: MopAliasPair) {
        self.alias_set.insert(alias);
    }
    pub fn len(&self) -> usize {
        self.alias_set.len()
    }
    pub fn sort_alias_index(&mut self) {
        let alias_set = std::mem::take(&mut self.alias_set);
        let mut new = HashSet::with_capacity(alias_set.len());
        for mut ra in alias_set {
            if ra.left_local() >= ra.right_local() {
                ra.swap();
            }
            new.insert(ra);
        }
        self.alias_set = new;
    }
}

pub type MopFnAliasMap = FxHashMap<DefId, MopFnAliasPairs>;

pub struct AliasAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub fn_map: FxHashMap<DefId, MopFnAliasPairs>,
    path_analyzer: PathAnalyzer<'tcx>,
}

impl<'tcx> Analysis for AliasAnalyzer<'tcx> {
    fn run(&mut self) {
        rap_debug!("Start alias analysis via MoP.");
        let mir_keys = self.tcx.mir_keys(());
        for local_def_id in mir_keys {
            self.query_alias_graph(local_def_id.to_def_id());
        }
        for (fn_id, fn_alias) in &mut self.fn_map {
            let fn_name = get_fn_name(self.tcx, *fn_id);
            fn_alias.sort_alias_index();
            if fn_alias.len() > 0 {
                rap_debug!("Alias found in {:?}: {}", fn_name, fn_alias);
            }
        }
        self.handle_conor_cases();
    }
}

impl<'tcx> AliasAnalysis for AliasAnalyzer<'tcx> {
    fn get_fn_alias(&self, def_id: DefId) -> Option<FnAliasPairs> {
        self.fn_map.get(&def_id).cloned().map(Into::into)
    }
    fn get_all_fn_alias(&self) -> FnAliasMap {
        self.fn_map
            .iter()
            .map(|(k, v)| (*k, FnAliasPairs::from(v.clone())))
            .collect()
    }
}

impl<'tcx> AliasAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            fn_map: FxHashMap::default(),
            path_analyzer: PathAnalyzer::new(tcx, false),
        }
    }

    fn handle_conor_cases(&mut self) {
        let cases = [
            copy_from_nonoverlapping_opt(),
            copy_to_nonoverlapping_opt(),
            copy_to_opt(),
            copy_from_opt(),
        ];
        let alias = MopAliasPair::new(1, true, true, 2, true, true);
        for (key, value) in self.fn_map.iter_mut() {
            if contains(&cases, *key) {
                value.alias_set.clear();
                value.alias_set.insert(alias.clone());
            }
        }
    }

    fn query_alias_graph(&mut self, def_id: DefId) {
        let fn_name = get_fn_name(self.tcx, def_id);
        if fn_name
            .as_ref()
            .map_or(false, |s| s.contains("__raw_ptr_deref_dummy"))
        {
            return;
        }
        if let Some(_other) = self.tcx.hir_body_const_context(def_id.expect_local()) {
            return;
        }
        if self.tcx.is_mir_available(def_id) {
            let paths = self.path_analyzer.analyze(def_id);
            let path_graph = self
                .path_analyzer
                .graphs
                .get(&def_id)
                .cloned()
                .unwrap_or_else(|| {
                    let mut g = crate::analysis::path::graph::PathGraph::new(self.tcx, def_id);
                    g.find_scc();
                    g
                });
            let mut alias_graph = AliasGraph::from_path_graph(self.tcx, def_id, path_graph);
            alias_graph.path_graph.find_scc();
            let mut recursion_set = HashSet::default();
            alias_graph.process_function_paths_opt(paths, &mut self.fn_map, &mut recursion_set);
            if alias_graph.visit_times() > VISIT_LIMIT {
                rap_trace!("Over visited: {:?}", def_id);
            }
            self.fn_map.insert(def_id, alias_graph.ret_alias);
        }
    }

    pub fn get_all_fn_alias_raw(&mut self) -> MopFnAliasMap {
        self.fn_map.clone()
    }
    pub fn take_path_analyzer(&mut self) -> PathAnalyzer<'tcx> {
        std::mem::replace(&mut self.path_analyzer, PathAnalyzer::new(self.tcx, false))
    }
}
