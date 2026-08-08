pub mod check_utils;
pub mod checking;
pub mod data_collection;
pub mod loop_visitors;
pub mod memory_cloning;
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

use lazy_static::lazy_static;
use std::sync::Mutex;

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
    fn report(&self, graph: &Graph);
    fn cnt(&self) -> usize;
}

impl<'tcx> Opt<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, level: usize) -> Self {
        Self { tcx, level }
    }

    pub fn start(&mut self) {
        let mut dataflow = DataflowAnalyzer::new(self.tcx, false);
        dataflow.build_graphs();
        {
            let mut no_std = NO_STD.lock().unwrap();
            *no_std = !has_crate(self.tcx, "std");
            let mut level = LEVEL.lock().unwrap();
            *level = self.level;
        }
        if !has_crate(self.tcx, "core") {
            //core it self
            return;
        }

        let mut statistics = vec![0 as usize; 6];

        dataflow.graphs.iter().for_each(|(_, graph)| {
            let mut bounds_check = BoundsCheck::new();
            bounds_check.check(graph, &self.tcx);
            statistics[0] += bounds_check.cnt();

            if self.level > 0 {
                bounds_check.report(graph);
            }

            let no_std = NO_STD.lock().unwrap();
            if !*no_std {
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

                if self.level > 0 {
                    encoding_check.report(graph);
                    suboptimal_check.report(graph);
                    initialization_check.report(graph);
                    reservation_check.report(graph);
                    used_as_immutable_check.report(graph);
                }
            }
        });

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
    }
}
