pub mod check_utils;
pub mod checking;
pub mod data_collection;
pub mod loop_visitors;
pub mod memory_cloning;
pub mod output;
pub mod report;

#[macro_export]
macro_rules! def_paths {
    ($($field:ident : $path:literal),+ $(,)?) => {
        static DEFPATHS: once_cell::sync::OnceCell<DefPaths> = once_cell::sync::OnceCell::new();
        struct DefPaths {
            $(pub $field: $crate::helpers::def_path::DefPath),+
        }
        impl DefPaths {
            #[allow(dead_code)]
            fn new(tcx: &rustc_middle::ty::TyCtxt<'_>) -> Self {
                Self {
                    $($field: $crate::helpers::def_path::DefPath::new($path, tcx)),+
                }
            }
        }
    };
}

use rustc_middle::ty::TyCtxt;

use crate::analysis::dataflow::{Graph, default::DataflowAnalyzer};
use crate::helpers::mir_utils::has_crate;
use checking::bounds_checking::BoundsCheck;
use checking::encoding_checking::EncodingCheck;
use data_collection::initialization::InitializationCheck;
use data_collection::reallocation::ReservationCheck;
use data_collection::suboptimal::SuboptimalCheck;
use memory_cloning::used_as_immutable::UsedAsImmutableCheck;
use report::{OptFinding, OptProfile, OptReport, RunStatus};

use lazy_static::lazy_static;
use std::{env, process::Command, sync::Mutex};

lazy_static! {
    pub(crate) static ref NO_STD: Mutex<bool> = Mutex::new(false);
    pub(crate) static ref LEVEL: Mutex<usize> = Mutex::new(0);
}

pub struct Opt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub level: usize,
}

pub trait OptCheck {
    fn new() -> Self;
    fn check(&mut self, graph: &Graph, tcx: &TyCtxt);
    /// Build the diagnostics once for terminal rendering and optional JSON export.
    fn report(&self, graph: &Graph) -> Vec<OptReport>;
    fn cnt(&self) -> usize;
}

impl<'tcx> Opt<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, level: usize) -> Self {
        Self { tcx, level }
    }

    pub fn start(&mut self, exporting: bool) {
        let output = if exporting {
            let rustc_args: Vec<String> = env::args().collect();
            let unit = crate::check::driver::unit_name(&rustc_args)
                .unwrap_or_else(|error| panic!("Cannot identify opt compilation unit: {error}"));
            let Some(directory) = output::create_unit_directory(&unit)
                .unwrap_or_else(|error| panic!("Cannot create opt unit directory: {error}"))
            else {
                return;
            };
            Some((unit, directory))
        } else {
            None
        };
        let no_std = !has_crate(self.tcx, "std");
        {
            *NO_STD.lock().unwrap() = no_std;
            let mut level = LEVEL.lock().unwrap();
            *level = self.level;
        }
        let mut statistics = [0_usize; 6];
        let mut findings = Vec::new();
        let mut analyzed_functions = 0;
        let mut limitations = Vec::new();

        if has_crate(self.tcx, "core") {
            let mut dataflow = DataflowAnalyzer::new(self.tcx, false);
            dataflow.build_graphs();
            if exporting {
                // RAPx injects these helpers even into a constant-only crate.
                // Count user functions while retaining the original checks below.
                analyzed_functions = dataflow
                    .graphs
                    .keys()
                    .filter(|def_id| {
                        !matches!(
                            self.tcx.def_path_str(**def_id).as_str(),
                            "__raw_ptr_deref_dummy" | "__static_mut_deref_dummy"
                        )
                    })
                    .count();
            }
            for graph in dataflow.graphs.values() {
                let mut bounds_check = BoundsCheck::new();
                bounds_check.check(graph, &self.tcx);
                statistics[0] += bounds_check.cnt();
                self.report_check(&bounds_check, graph, exporting, &mut findings);

                if !no_std {
                    let mut encoding_check = EncodingCheck::new();
                    encoding_check.check(graph, &self.tcx);
                    statistics[1] += encoding_check.cnt();

                    let mut suboptimal_check = SuboptimalCheck::new();
                    suboptimal_check.check(graph, &self.tcx);
                    statistics[2] += suboptimal_check.cnt();

                    let mut initialization_check = InitializationCheck::new();
                    initialization_check.check(graph, &self.tcx);
                    statistics[3] += initialization_check.cnt();

                    let mut reservation_check = ReservationCheck::new();
                    reservation_check.check(graph, &self.tcx);
                    statistics[4] += reservation_check.cnt();

                    let mut used_as_immutable_check = UsedAsImmutableCheck::new();
                    used_as_immutable_check.check(graph, &self.tcx);
                    statistics[5] += used_as_immutable_check.cnt();

                    self.report_check(&encoding_check, graph, exporting, &mut findings);
                    self.report_check(&suboptimal_check, graph, exporting, &mut findings);
                    self.report_check(&initialization_check, graph, exporting, &mut findings);
                    self.report_check(&reservation_check, graph, exporting, &mut findings);
                    self.report_check(&used_as_immutable_check, graph, exporting, &mut findings);
                }
            }
        } else {
            limitations.push("core_crate_unavailable".into());
        }

        let bug_cnt: usize = statistics.iter().sum();
        if bug_cnt > 0 {
            rap_warn!("Potential optimizations detected.");
            rap_info!(
                "  Bounds Checking: {}, Encoding Checking: {}, Suboptimal: {}, Initialization: {}, Reallocation: {}, Cloning: {}",
                statistics[0],
                statistics[1],
                statistics[2],
                statistics[3],
                statistics[4],
                statistics[5],
            );
        }
        if let Some((unit, directory)) = output {
            let status = if analyzed_functions == 0 {
                limitations.push("no_functions_analyzed".into());
                RunStatus::Skipped
            } else {
                RunStatus::Completed
            };
            let profile = OptProfile {
                schema_version: 1,
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
                level: self.level,
                no_std,
                analyzed_functions,
                finding_count: findings.len(),
                statistics,
                limitations,
            };
            output::write_reports(&directory, profile, findings)
                .unwrap_or_else(|error| panic!("Failed to export opt context: {error}"));
            rap_info!("opt profile: {}", directory.join("profile.json").display());
        }
    }

    fn report_check(
        &self,
        check: &impl OptCheck,
        graph: &Graph,
        exporting: bool,
        findings: &mut Vec<OptFinding>,
    ) {
        if self.level == 0 && !exporting {
            return;
        }
        for report in check.report(graph) {
            if self.level > 0 {
                report.emit();
            }
            if exporting {
                findings.push(report.into_finding(self.tcx.def_path_str(graph.def_id)));
            }
        }
    }
}
