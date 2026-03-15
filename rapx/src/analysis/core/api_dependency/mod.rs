mod fuzzable;
/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.

#[allow(unused)]
pub mod graph;
mod mono;
mod utils;
#[allow(unused)]
mod visit;

use crate::analysis::Analysis;
pub use graph::ApiDependencyGraph;
pub use graph::{DepEdge, DepNode};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use serde::Serialize;
use std::path::PathBuf;
pub use utils::{is_def_id_public, is_fuzzable_ty};
pub use visit::Config as VisitConfig;

#[derive(Debug, Clone, Serialize)]
pub struct StatsWithCoverage {
    pub num_apis: usize,
    pub num_generic_apis: usize,
    pub num_covered_apis: usize,
    pub num_covered_generic_apis: usize,
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd)]
pub struct Config {
    pub resolve_generic: bool,
    pub visit_config: visit::Config,
    pub max_generic_search_iteration: usize,
    pub dump: Option<PathBuf>,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            resolve_generic: true,
            visit_config: VisitConfig::default(),
            max_generic_search_iteration: 10,
            dump: None,
        }
    }
}

pub trait ApiDependencyAnalysis<'tcx> {
    fn get_api_dependency_graph(&self) -> ApiDependencyGraph<'tcx>;
}

pub struct ApiDependencyAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    config: Config,
    api_graph: ApiDependencyGraph<'tcx>,
}

impl<'tcx> ApiDependencyAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, config: Config) -> ApiDependencyAnalyzer<'tcx> {
        ApiDependencyAnalyzer {
            tcx,
            config,
            api_graph: ApiDependencyGraph::new(tcx),
        }
    }
}

impl<'tcx> Analysis for ApiDependencyAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Default API dependency graph analysis algorithm."
    }

    fn run(&mut self) {
        let local_crate_name = self.tcx.crate_name(LOCAL_CRATE);
        let local_crate_type = self.tcx.crate_types()[0];
        rap_info!(
            "Build API dependency graph on {} ({}), config = {:?}",
            local_crate_name.as_str(),
            local_crate_type,
            self.config,
        );

        let api_graph = &mut self.api_graph;
        api_graph.build(&self.config);

        let stats = api_graph.statistics();
        stats.info();
        let mut num_covered_apis = 0;
        let mut num_covered_generic_apis = 0;
        let mut num_total = 0;

        api_graph.traverse_covered_api_with(
            &mut |did| {
                num_covered_apis += 1;
                if utils::fn_requires_monomorphization(did, self.tcx) {
                    num_covered_generic_apis += 1;
                }
            },
            &mut |_| {
                num_total += 1;
            },
        );

        rap_info!("uncovered APIs: {:?}", api_graph.uncovered_api());

        rap_info!(
            "Cov API/Cov GAPI/#API/#GAPI: {}({:.2})/{}({:.2})/{}/{}",
            num_covered_apis,
            num_covered_apis as f64 / stats.num_api as f64,
            num_covered_generic_apis,
            num_covered_generic_apis as f64 / stats.num_generic_api as f64,
            stats.num_api,
            stats.num_generic_api
        );

        let stats_with_coverage = StatsWithCoverage {
            num_apis: stats.num_api,
            num_generic_apis: stats.num_generic_api,
            num_covered_apis,
            num_covered_generic_apis,
        };

        // dump adg stats
        let stats_file = std::fs::File::create("adg_stats.json").unwrap();
        serde_json::to_writer(stats_file, &stats_with_coverage)
            .expect("failed to dump stats to JSON");

        // dump API graph, determine the format base on extension name
        if let Some(dump_path) = &self.config.dump {
            self.api_graph
                .dump_to_file(dump_path)
                .inspect_err(|err| {
                    rap_error!("{:?}", err);
                })
                .expect("failed to dump API graph");
        }
    }

    fn reset(&mut self) {
        todo!();
    }
}

impl<'tcx> ApiDependencyAnalysis<'tcx> for ApiDependencyAnalyzer<'tcx> {
    fn get_api_dependency_graph(&self) -> ApiDependencyGraph<'tcx> {
        self.api_graph.clone()
    }
}
