mod capture;
pub mod output;
pub mod ranalyzer;
pub mod report;

use crate::analysis::{
    Analysis,
    heap_ownership::{
        HeapOwnershipAnalysis, HeapOwnershipResultMap, default::HeapOwnershipAnalyzer,
    },
};
use ranalyzer::{FlowAnalysis, IcxSliceFroBlock, IntraFlowContext, MirGraph};
use rustc_middle::ty::TyCtxt;
use std::{collections::HashMap, env, process::Command};

use report::{AnalysisReport, RCanaryProfile, RunStatus};

pub(crate) const SOLVER_TIMEOUT_MS: u64 = 1000;

#[allow(non_camel_case_types)]
#[derive(Clone)]
pub struct rCanary<'tcx> {
    tcx: TyCtxt<'tcx>,
    adt_owner: HeapOwnershipResultMap,
    mir_graph: MirGraph,
}

impl<'tcx> rCanary<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, adt_owner: HeapOwnershipResultMap) -> Self {
        Self {
            tcx,
            adt_owner,
            mir_graph: HashMap::default(),
        }
    }

    pub fn start(&mut self, exporting: bool) {
        let output = if exporting {
            let rustc_args: Vec<_> = env::args().collect();
            let unit = crate::check::driver::unit_name(&rustc_args)
                .unwrap_or_else(|err| panic!("Cannot identify rCanary compilation unit: {err}"));
            let Some(directory) = output::create_unit_directory(&unit)
                .unwrap_or_else(|err| panic!("Cannot create rCanary unit directory: {err}"))
            else {
                return;
            };
            Some((unit, directory))
        } else {
            None
        };
        let mut report = exporting.then(AnalysisReport::default);
        let mut heap = HeapOwnershipAnalyzer::new(self.tcx);
        heap.run();
        let adt_owner = heap.get_all_items();
        let rcx_boxed = Box::new(rCanary::new(self.tcx, adt_owner));
        // Leak to create a 'static reference needed for FlowAnalysis lifetime.
        let rcx = Box::leak(rcx_boxed);
        FlowAnalysis::new(rcx).start(report.as_mut());
        if let Some((unit, directory)) = output {
            let mut report = report.expect("rCanary report collection was enabled");
            let status = if report.analyzed_functions == 0 {
                report.limitations.push("no_functions_analyzed".into());
                RunStatus::Skipped
            } else if report.limitations.is_empty() {
                RunStatus::Completed
            } else {
                RunStatus::Partial
            };
            let finding_count = report.findings.len();
            let profile = RCanaryProfile {
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
                analyzed_functions: report.analyzed_functions,
                skipped_functions: report.skipped_functions,
                checked_returns: report.checked_returns,
                finding_count,
                solver_timeout_ms: SOLVER_TIMEOUT_MS,
                limitations: std::mem::take(&mut report.limitations),
            };
            output::write_reports(&directory, profile, report)
                .unwrap_or_else(|err| panic!("Failed to export rCanary context: {err}"));
            rap_info!(
                "rCanary profile: {} ({finding_count} findings)",
                directory.join("profile.json").display()
            );
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn adt_owner(&self) -> &HeapOwnershipResultMap {
        &self.adt_owner
    }

    pub fn mir_graph(&self) -> &MirGraph {
        &self.mir_graph
    }

    pub fn mir_graph_mut(&mut self) -> &mut MirGraph {
        &mut self.mir_graph
    }
}

pub trait Tcx<'tcx, 'o, 'a> {
    fn tcx(&'o self) -> TyCtxt<'tcx>;
}

pub trait Rcx<'tcx, 'o, 'a> {
    fn rcx(&'o self) -> &'a rCanary<'tcx>;

    fn tcx(&'o self) -> TyCtxt<'tcx>;
}

pub trait RcxMut<'tcx, 'o, 'a> {
    fn rcx(&'o self) -> &'o rCanary<'tcx>;

    fn rcx_mut(&'o mut self) -> &'o mut rCanary<'tcx>;

    fn tcx(&'o self) -> TyCtxt<'tcx>;
}

pub trait IcxMut<'tcx, 'z3, 'o> {
    fn icx(&'o self) -> &'o IntraFlowContext<'tcx, 'z3>;

    fn icx_mut(&'o mut self) -> &'o mut IntraFlowContext<'tcx, 'z3>;
}

pub trait IcxSliceMut<'tcx, 'z3, 'o> {
    fn icx_slice(&'o self) -> &'o IcxSliceFroBlock<'tcx, 'z3>;

    fn icx_slice_mut(&'o mut self) -> &'o mut IcxSliceFroBlock<'tcx, 'z3>;
}
