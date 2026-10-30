pub mod bug_records;
mod capture;
pub mod checks;
pub mod corner_case;
pub mod driver;
pub mod drop;
pub mod graph;
pub mod observer;
pub mod output;
pub mod report;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::{collections::BTreeMap, env, process::Command};

use crate::limit::SAFEDROP_VISIT_LIMIT;
use crate::{
    analysis::{
        alias::default::{AliasAnalyzer, MopFnAliasMap},
        heap_ownership::{
            HeapOwnershipAnalysis, HeapOwnershipResultMap, default::HeapOwnershipAnalyzer,
        },
        path::default::PathAnalyzer,
    },
    utils::source::get_fn_name,
};
use graph::SafeDropGraph;

use crate::analysis::Analysis;

pub struct SafeDrop<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> SafeDrop<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
    pub fn start(&self, exporting: bool) {
        let output = if exporting {
            let rustc_args: Vec<String> = env::args().collect();
            let unit = driver::unit_name(&rustc_args)
                .unwrap_or_else(|err| panic!("Cannot identify SafeDrop compilation unit: {err}"));
            let Some(directory) = output::create_unit_directory(&unit)
                .unwrap_or_else(|err| panic!("Cannot create SafeDrop unit directory: {err}"))
            else {
                return;
            };
            Some((unit, directory))
        } else {
            None
        };
        let mut mop = AliasAnalyzer::new(self.tcx);
        mop.run();
        let fn_map = mop.get_all_fn_alias_raw();
        let path_analyzer = mop.take_path_analyzer();
        rap_info!("================================");
        rap_debug!("Aliases found: {:?}", fn_map);

        let mut heap = HeapOwnershipAnalyzer::new(self.tcx);
        heap.run();
        let adt_owner = heap.get_all_items();

        let mir_keys = self.tcx.mir_keys(());
        let mut findings = Vec::new();
        let mut functions = BTreeMap::new();
        let mut analyzed_functions = 0;
        let mut incomplete = false;
        let mut limitations = Vec::new();
        for local_def_id in mir_keys {
            if let Some(graph) = query_safedrop(
                self.tcx,
                &fn_map,
                local_def_id.to_def_id(),
                adt_owner.clone(),
                &path_analyzer,
                exporting,
            ) {
                if exporting {
                    analyzed_functions += 1;
                    let function = self.tcx.def_path_str(local_def_id.to_def_id());
                    if graph.analysis_incomplete {
                        incomplete = true;
                        let reason = if graph.alias_graph.visit_times() > SAFEDROP_VISIT_LIMIT {
                            "safedrop_visit_limit_reached"
                        } else {
                            "no_enumerated_path"
                        };
                        limitations.push(format!("{function}: {reason}"));
                    }
                    let function_findings = capture::findings(&graph);
                    if !function_findings.is_empty() {
                        let context = capture::function_context(&graph);
                        functions.insert(function, context);
                    }
                    findings.extend(function_findings);
                }
            }
        }
        if let Some((unit, directory)) = output {
            let status = if analyzed_functions == 0 {
                limitations.push("no_functions_analyzed".into());
                report::RunStatus::Skipped
            } else if incomplete {
                report::RunStatus::Partial
            } else {
                report::RunStatus::Completed
            };
            let profile = report::SafeDropProfile {
                unit,
                rapx_version: env!("CARGO_PKG_VERSION").into(),
                rustc_version: Command::new("rustc")
                    .arg("--version")
                    .output()
                    .ok()
                    .filter(|out| out.status.success())
                    .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_owned()),
                working_directory: env::current_dir()
                    .expect("Current working directory invalid.")
                    .to_string_lossy()
                    .into_owned(),
                status,
                analyzed_functions,
                limitations,
            };
            let finding_count = findings.len();
            output::write_reports(&directory, profile, &functions, findings)
                .unwrap_or_else(|error| panic!("Failed to export SafeDrop context: {error}"));
            rap_info!(
                "SafeDrop profile: {} ({finding_count} findings)",
                directory.join("profile.json").display()
            );
        }
    }
}

pub fn query_safedrop<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_map: &MopFnAliasMap,
    def_id: DefId,
    adt_owner: HeapOwnershipResultMap,
    path_analyzer: &PathAnalyzer<'tcx>,
    exporting: bool,
) -> Option<SafeDropGraph<'tcx>> {
    let fn_name = get_fn_name(tcx, def_id);
    if fn_name
        .as_ref()
        .is_some_and(|s| s.contains("__raw_ptr_deref_dummy"))
    {
        return None;
    }
    rap_trace!("query_safedrop: {:?}", fn_name);
    /* filter const mir */
    if let Some(_other) = tcx.hir_body_const_context(def_id.expect_local()) {
        return None;
    }
    if tcx.is_mir_available(def_id) {
        let paths = path_analyzer.get_fn_paths(def_id);
        let path_graph = path_analyzer
            .graphs
            .get(&def_id)
            .cloned()
            .unwrap_or_else(|| {
                let mut g = crate::analysis::path::graph::PathGraph::new(tcx, def_id);
                g.find_scc();
                g
            });
        let mut safedrop_graph =
            SafeDropGraph::from_path_graph(tcx, def_id, path_graph, adt_owner, exporting);
        rap_debug!("safedrop grah (raw): {}", safedrop_graph);
        safedrop_graph.alias_graph.path_graph.find_scc();
        rap_debug!("safedrop graph (scc): {}", safedrop_graph);
        safedrop_graph.process_function_paths_opt(paths, fn_map);
        let visit_times = safedrop_graph.alias_graph.visit_times();
        if visit_times <= SAFEDROP_VISIT_LIMIT || !safedrop_graph.bug_records.is_bug_free() {
            safedrop_graph.report_bugs();
        }
        return Some(safedrop_graph);
    }
    None
}
