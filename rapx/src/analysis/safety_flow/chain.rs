use crate::helpers::mir_scan::check_safety;
use crate::helpers::mir_utils::dep_callee_def_id;
use crate::helpers::name::get_cleaned_def_path_name;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{Terminator, TerminatorKind},
    ty::TyCtxt,
};
use std::collections::HashSet;

/// DFS-based unsafe call chain analysis.
///
/// Starting from `def_id`, traverses all callees that are `unsafe fn`,
/// collecting paths until a leaf (function with no unsafe callees) is reached.
pub fn get_all_std_unsafe_chains(tcx: TyCtxt, def_id: DefId) -> Vec<Vec<String>> {
    let mut results = Vec::new();
    let mut visited = HashSet::new();
    let mut current_chain = Vec::new();

    dfs_find_unsafe_chains(tcx, def_id, &mut current_chain, &mut results, &mut visited);
    results
}

fn dfs_find_unsafe_chains(
    tcx: TyCtxt,
    def_id: DefId,
    current_chain: &mut Vec<String>,
    results: &mut Vec<Vec<String>>,
    visited: &mut HashSet<DefId>,
) {
    if visited.contains(&def_id) {
        return;
    }
    visited.insert(def_id);

    let current_func_name = get_cleaned_def_path_name(tcx, def_id);
    current_chain.push(current_func_name.clone());

    let unsafe_callees = find_unsafe_callees_in_function(tcx, def_id);

    if unsafe_callees.is_empty() {
        results.push(current_chain.clone());
    } else {
        for (callee_def_id, _callee_name) in unsafe_callees {
            dfs_find_unsafe_chains(tcx, callee_def_id, current_chain, results, visited);
        }
    }

    current_chain.pop();
    visited.remove(&def_id);
}

fn find_unsafe_callees_in_function(tcx: TyCtxt, def_id: DefId) -> Vec<(DefId, String)> {
    let mut callees = Vec::new();

    if let Some(body) = try_get_mir(tcx, def_id) {
        for bb in body.basic_blocks.iter() {
            if let Some(terminator) = &bb.terminator {
                if let Some((callee_def_id, callee_name)) = extract_unsafe_callee(tcx, terminator) {
                    callees.push((callee_def_id, callee_name));
                }
            }
        }
    }

    callees
}

fn extract_unsafe_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Option<(DefId, String)> {
    if let TerminatorKind::Call { func, .. } = &terminator.kind {
        if let Some(callee_def_id) = dep_callee_def_id(func) {
            if check_safety(tcx, callee_def_id) == Safety::Unsafe {
                let func_name = get_cleaned_def_path_name(tcx, callee_def_id);
                return Some((callee_def_id, func_name));
            }
        }
    }
    None
}

fn try_get_mir(tcx: TyCtxt<'_>, def_id: DefId) -> Option<&rustc_middle::mir::Body<'_>> {
    if tcx.is_mir_available(def_id) {
        Some(tcx.optimized_mir(def_id))
    } else {
        None
    }
}

pub fn print_unsafe_chains(chains: &[Vec<String>]) {
    if chains.is_empty() {
        return;
    }

    println!("==============================");
    println!("Found {} unsafe call chain(s):", chains.len());
    for (i, chain) in chains.iter().enumerate() {
        println!("Chain {}:", i + 1);
        for (j, func_name) in chain.iter().enumerate() {
            let indent = "  ".repeat(j);
            println!("{}{}-> {}", indent, if j > 0 { " " } else { "" }, func_name);
        }
        println!();
    }
}
