pub mod checking;
pub mod data_collection;
pub mod iterator;
pub mod memory_cloning;

use rustc_middle::ty::TyCtxt;

use crate::utils::log::span_to_source_code;

use crate::analysis::core::dataflow::{default::DataFlowAnalyzer, Graph};
use checking::bounds_checking::BoundsCheck;
use checking::encoding_checking::EncodingCheck;
use data_collection::initialization::InitializationCheck;
use data_collection::reallocation::ReservationCheck;
use data_collection::suboptimal::SuboptimalCheck;
use memory_cloning::used_as_immutable::UsedAsImmutableCheck;

use lazy_static::lazy_static;
use rustc_span::symbol::Symbol;
use std::sync::Mutex;

lazy_static! {
    pub static ref NO_STD: Mutex<bool> = Mutex::new(false);
    pub static ref LEVEL: Mutex<usize> = Mutex::new(0);
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

    fn has_crate(&self, name: &str) -> bool {
        for num in self.tcx.crates(()) {
            if self.tcx.crate_name(*num) == Symbol::intern(name) {
                return true;
            }
        }
        false
    }

    pub fn start(&mut self) {
        let mut dataflow = DataFlowAnalyzer::new(self.tcx, false);
        dataflow.build_graphs();
        {
            let mut no_std = NO_STD.lock().unwrap();
            *no_std = !self.has_crate("std");
            let mut level = LEVEL.lock().unwrap();
            *level = self.level;
        }
        if !self.has_crate("core") {
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
        let func_cnt: usize = dataflow.graphs.iter().count();
        let line_cnt: usize = dataflow
            .graphs
            .iter()
            .map(|(_, graph)| span_to_source_code(graph.span).lines().count())
            .sum();
        if bug_cnt > 0 {
            rap_warn!("Potential optimizations detected.");
            println!(
                "RAPx detects {} code inefficiencies from {} functions ({} lines)",
                bug_cnt, func_cnt, line_cnt,
            );
            println!("  Bounds Checking: {}", statistics[0]);
            println!("  Encoding Checking: {}", statistics[1]);
            println!("  Suboptimal: {}", statistics[2]);
            println!("  Initialization: {}", statistics[3]);
            println!("  Reallocation: {}", statistics[4]);
            println!("  Cloning: {}", statistics[5]);
        }
    }
}
