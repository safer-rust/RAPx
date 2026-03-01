#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(macro_metavar_expr_concat)]

#[macro_use]
pub mod utils;
pub mod analysis;
pub mod cli;
pub mod def_id;
pub mod help;
pub mod preprocess;
extern crate intervals;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_traits;
extern crate rustc_type_ir;
extern crate thin_vec;
use crate::{
    analysis::{core::alias_analysis::mfp::MfpAliasAnalyzer, scan::ScanAnalysis},
    cli::{AliasStrategyKind, AnalysisKind, Commands, OptLevel, RapxArgs},
};
use analysis::{
    Analysis,
    core::{
        alias_analysis::{AliasAnalysis, FnAliasMapWrapper, default::AliasAnalyzer},
        api_dependency::ApiDependencyAnalyzer,
        callgraph::{CallGraphAnalysis, FnCallDisplay, default::CallGraphAnalyzer},
        dataflow::{
            Arg2RetMapWrapper, DataFlowAnalysis, DataFlowGraphMapWrapper, default::DataFlowAnalyzer,
        },
        ownedheap_analysis::{OHAResultMapWrapper, OwnedHeapAnalysis, default::OwnedHeapAnalyzer},
        range_analysis::{
            PathConstraintMapWrapper, RAResultMapWrapper, RangeAnalysis, default::RangeAnalyzer,
        },
        ssa_transform::SSATrans,
    },
    opt::Opt,
    rcanary::rCanary,
    safedrop::SafeDrop,
    senryx::{CheckLevel, SenryxCheck},
    upg::{TargetCrate, UPGAnalysis},
    utils::show_mir::ShowMir,
};
use rustc_ast::ast;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface::{self, Compiler};
use rustc_middle::{ty::TyCtxt, util::Providers};
use rustc_session::search_paths::PathKind;
use std::path::PathBuf;
use std::sync::Arc;

pub static RAP_DEFAULT_ARGS: &[&str] = &[
    "-Zalways-encode-mir",
    "-Zmir-opt-level=0",
    "-Zinline-mir-threshold=0",
    "-Zinline-mir-hint-threshold=0",
    "-Zcross-crate-inline-threshold=0",
];

/// This is the data structure to handle rapx options as a rustc callback.

#[derive(Debug, Clone)]
pub struct RapCallback {
    args: RapxArgs,
}

impl RapCallback {
    pub fn new(args: RapxArgs) -> Self {
        Self { args }
    }

    fn is_building_test_crate(&self) -> bool {
        match &self.args.test_crate {
            None => true,
            Some(test_crate) => {
                let test_crate: &str = test_crate;
                let package_name = std::env::var("CARGO_PKG_NAME")
                    .expect("cannot capture env var `CARGO_PKG_NAME`");
                package_name == test_crate
            }
        }
    }
}

impl Callbacks for RapCallback {
    fn config(&mut self, config: &mut rustc_interface::Config) {
        config.override_queries = Some(|_, providers| {
            providers.extern_queries.used_crate_source = |tcx, cnum| {
                let mut providers = Providers::default();
                rustc_metadata::provide(&mut providers);
                let mut crate_source = (providers.extern_queries.used_crate_source)(tcx, cnum);
                // HACK: rustc will emit "crate ... required to be available in rlib format, but
                // was not found in this form" errors once we use `tcx.dependency_formats()` if
                // there's no rlib provided, so setting a dummy path here to workaround those errors.
                Arc::make_mut(&mut crate_source).rlib = Some((PathBuf::new(), PathKind::All));
                crate_source
            };
        });
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &interface::Compiler,
        krate: &mut ast::Crate,
    ) -> Compilation {
        let build_std = compiler
            .sess
            .opts
            .crate_name
            .as_deref()
            .map(|s| matches!(s, "core" | "std"))
            .unwrap_or(false);
        preprocess::dummy_fns::create_dummy_fns(krate, build_std);
        preprocess::ssa_preprocess::create_ssa_struct(krate, build_std);
        Compilation::Continue
    }
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        rap_trace!("Execute after_analysis() of compiler callbacks");

        rustc_public::rustc_internal::run(tcx, || {
            def_id::init(tcx);
            if self.is_building_test_crate() {
                start_analyzer(tcx, self);
            } else {
                let package_name = std::env::var("CARGO_PKG_NAME")
                    .expect("cannot capture env var `CARGO_PKG_NAME`");
                rap_trace!("skip analyzing package `{}`", package_name);
            }
        })
        .expect("Failed to run rustc_public.");
        rap_trace!("analysis done");

        Compilation::Continue
    }
}

/// Start the analysis with the features enabled.
pub fn start_analyzer(tcx: TyCtxt, callback: &RapCallback) {
    match &callback.args.command {
        &Commands::Check {
            uaf,
            mleak,
            opt,
            infer,
            verify,
            verify_std,
        } => {
            if uaf.is_some() {
                SafeDrop::new(tcx).start();
            }
            if mleak {
                let mut heap = OwnedHeapAnalyzer::new(tcx);
                heap.run();
                let adt_owner = heap.get_all_items();
                rCanary::new(tcx, adt_owner).start();
            }
            if let Some(opt_level) = opt {
                match opt_level {
                    OptLevel::Report => Opt::new(tcx, 0).start(),
                    OptLevel::Default => Opt::new(tcx, 1).start(),
                    OptLevel::All => Opt::new(tcx, 2).start(),
                }
            }
            if infer {
                let check_level = CheckLevel::Medium;
                SenryxCheck::new(tcx, 2).start(check_level, false);
            }
            if verify {
                let check_level = CheckLevel::Medium;
                SenryxCheck::new(tcx, 2).start(check_level, true);
            }

            if verify_std {
                SenryxCheck::new(tcx, 2).start_analyze_std_func();
                // SenryxCheck::new(tcx, 2).generate_uig_by_def_id();
            }
        }

        &Commands::Analyze { kind } => match kind {
            AnalysisKind::Alias { strategy } => {
                let alias = match strategy {
                    AliasStrategyKind::Mop => {
                        let mut analyzer = AliasAnalyzer::new(tcx);
                        analyzer.run();
                        analyzer.get_local_fn_alias()
                    }
                    AliasStrategyKind::Mfp => {
                        let mut analyzer = MfpAliasAnalyzer::new(tcx);
                        analyzer.run();
                        analyzer.get_local_fn_alias()
                    }
                };
                rap_info!("{}", FnAliasMapWrapper(alias));
            }
            AnalysisKind::Adg => {
                let mut analyzer = ApiDependencyAnalyzer::new(
                    tcx,
                    analysis::core::api_dependency::Config {
                        pub_only: true,
                        resolve_generic: true,
                        ignore_const_generic: true,
                    },
                );
                analyzer.run();
            }
            AnalysisKind::Upg => {
                UPGAnalysis::new(tcx).start(TargetCrate::Other);
            }
            AnalysisKind::UpgStd => {
                UPGAnalysis::new(tcx).start(TargetCrate::Std);
            }
            AnalysisKind::Callgraph => {
                let mut analyzer = CallGraphAnalyzer::new(tcx);
                analyzer.run();
                let callgraph = analyzer.get_fn_calls();
                rap_info!(
                    "{}",
                    FnCallDisplay {
                        fn_calls: &callgraph,
                        tcx
                    }
                );
            }
            AnalysisKind::Dataflow { debug } => {
                if debug {
                    let mut analyzer = DataFlowAnalyzer::new(tcx, true);
                    analyzer.run();
                    let result = analyzer.get_all_dataflow();
                    rap_info!("{}", DataFlowGraphMapWrapper(result));
                } else {
                    let mut analyzer = DataFlowAnalyzer::new(tcx, false);
                    analyzer.run();
                    let result = analyzer.get_all_arg2ret();
                    rap_info!("{}", Arg2RetMapWrapper(result));
                }
            }
            AnalysisKind::OwnedHeap => {
                let mut analyzer = OwnedHeapAnalyzer::new(tcx);
                analyzer.run();
                let result = analyzer.get_all_items();
                rap_info!("{}", OHAResultMapWrapper(result));
            }
            AnalysisKind::Pathcond => {
                let mut analyzer = RangeAnalyzer::<i64>::new(tcx, false);
                analyzer.start_path_constraints_analysis();
                let result = analyzer.get_all_path_constraints();
                rap_info!("{}", PathConstraintMapWrapper(result));
            }
            AnalysisKind::Range { debug } => {
                let mut analyzer = RangeAnalyzer::<i64>::new(tcx, debug);
                analyzer.run();
                let result = analyzer.get_all_fn_ranges();
                rap_info!("{}", RAResultMapWrapper(result));
            }

            AnalysisKind::Scan => {
                ScanAnalysis::new(tcx).run();
            }
            AnalysisKind::Mir => {
                ShowMir::new(tcx).start();
            }
            AnalysisKind::DotMir => {
                ShowMir::new(tcx).start_generate_dot();
            }
            AnalysisKind::Ssa => {
                SSATrans::new(tcx, false).start();
            }
        },
    }
}
