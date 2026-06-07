pub mod alias;
pub mod assign;
pub mod block;
pub mod graph;
pub mod mop;
pub mod types;
pub mod value;

use super::{AliasAnalysis, AliasPair, FnAliasMap, FnAliasPairs};
use crate::{analysis::Analysis, def_id::*, utils::source::*};
use graph::AliasGraph;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::{cmp::Ordering, collections::HashSet, convert::From, fmt};

pub const VISIT_LIMIT: usize = 1000;

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

    pub fn valuable(&self) -> bool {
        return self.lhs_may_drop && self.rhs_may_drop;
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
        let alias_set = m.alias_set.into_iter().map(Into::into).collect(); // MopAliasPair -> AliasPair
        FnAliasPairs {
            arg_size: m.arg_size,
            alias_set,
        }
    }
}

impl PartialOrd for MopAliasPair {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MopAliasPair {
    fn cmp(&self, other: &Self) -> Ordering {
        self.fact
            .left_local
            .cmp(&other.fact.left_local)
            .then_with(|| self.fact.lhs_fields.cmp(&other.fact.lhs_fields))
            .then_with(|| self.fact.right_local.cmp(&other.fact.right_local))
            .then_with(|| self.fact.rhs_fields.cmp(&other.fact.rhs_fields))
            .then_with(|| self.lhs_may_drop.cmp(&other.lhs_may_drop))
            .then_with(|| self.lhs_need_drop.cmp(&other.lhs_need_drop))
            .then_with(|| self.rhs_may_drop.cmp(&other.rhs_may_drop))
            .then_with(|| self.rhs_need_drop.cmp(&other.rhs_need_drop))
    }
}

impl fmt::Display for MopAliasPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.fact)
    }
}

#[derive(Debug, Clone)]
pub struct MopFnAliasPairs {
    arg_size: usize,
    alias_set: HashSet<MopAliasPair>,
}

impl fmt::Display for MopFnAliasPairs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.aliases()
                .iter()
                .map(|alias| format!("{}", alias.fact))
                .collect::<Vec<String>>()
                .join(",")
        )
    }
}

impl MopFnAliasPairs {
    pub fn new(arg_size: usize) -> MopFnAliasPairs {
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
        let mut new_alias_set = HashSet::with_capacity(alias_set.len());

        for mut ra in alias_set.into_iter() {
            if ra.left_local() >= ra.right_local() {
                ra.swap();
            }
            new_alias_set.insert(ra);
        }
        self.alias_set = new_alias_set;
    }
}

//struct to cache the results for analyzed functions.
pub type MopFnAliasMap = FxHashMap<DefId, MopFnAliasPairs>;

pub struct AliasAnalyzer<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub fn_map: FxHashMap<DefId, MopFnAliasPairs>,
}

impl<'tcx> Analysis for AliasAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Alias Analysis (MoP)"
    }

    fn run(&mut self) {
        rap_debug!("Start alias analysis via MoP.");
        let mir_keys = self.tcx.mir_keys(());
        for local_def_id in mir_keys {
            self.query_alias_graph(local_def_id.to_def_id());
        }
        // Meaning of output: 0 for ret value; 1,2,3,... for corresponding args.
        for (fn_id, fn_alias) in &mut self.fn_map {
            let fn_name = get_fn_name(self.tcx, *fn_id);
            fn_alias.sort_alias_index();
            if fn_alias.len() > 0 {
                rap_debug!("Alias found in {:?}: {}", fn_name, fn_alias);
            }
        }
        self.handle_conor_cases();
    }

    fn reset(&mut self) {
        todo!();
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
        rap_trace!("query_alias_graph: {:?}", fn_name);
        /* filter const mir */
        if let Some(_other) = self.tcx.hir_body_const_context(def_id.expect_local()) {
            return;
        }

        if self.tcx.is_mir_available(def_id) {
            let mut alias_graph = AliasGraph::new(self.tcx, def_id);
            rap_debug!("Alias graph created: {}", alias_graph);
            rap_debug!("Search scc components in the graph.");
            alias_graph.find_scc();
            rap_trace!("After searching scc: {}", alias_graph);
            let mut recursion_set = HashSet::default();
            alias_graph.check(0, &mut self.fn_map, &mut recursion_set);
            if alias_graph.visit_times() > VISIT_LIMIT {
                rap_trace!("Over visited: {:?}", def_id);
            }
            self.fn_map.insert(def_id, alias_graph.ret_alias);
        } else {
            rap_trace!("Mir is not available at {}", self.tcx.def_path_str(def_id));
        }
    }

    pub fn get_all_fn_alias_raw(&mut self) -> MopFnAliasMap {
        self.fn_map.clone()
    }
}
