pub mod default;
pub mod visitor;

use crate::Analysis;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::{collections::HashMap, fmt};

pub type FnCallMap = HashMap<DefId, Vec<DefId>>; // caller_id -> Vec<(callee_id)>

pub struct FnCallDisplay<'a, 'tcx> {
    pub fn_calls: &'a FnCallMap,
    pub tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> fmt::Display for FnCallDisplay<'a, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "CallGraph:")?;
        for (caller, callees) in self.fn_calls {
            let caller_name = self.tcx.def_path_str(*caller);
            writeln!(f, "  {} calls:", caller_name)?;
            for callee in callees {
                let callee_name = self.tcx.def_path_str(*callee);
                writeln!(f, "    -> {}", callee_name)?;
            }
        }
        Ok(())
    }
}

/// This trait provides features related to call graph extraction and analysis.
pub trait CallGraphAnalysis: Analysis {
    /// Return the call graph.
    fn get_fn_calls(&self) -> FnCallMap;
}
