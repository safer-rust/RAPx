pub mod default;
pub mod graph;

use crate::utils::source::get_fn_name_byid;
use rustc_hir::def_id::DefId;
use std::fmt::{self, Display};

use rustc_data_structures::fx::FxHashMap;

pub type PathSet = Vec<Vec<usize>>;
pub type PathMap = FxHashMap<DefId, PathSet>;
pub struct PathMapWrapper(pub PathMap);

impl Display for PathMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print path analysis results ===")?;
        for (def_id, paths) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Function: {:?}:", fn_name)?;
            for path in paths {
                writeln!(f, "  Path {:?}", path)?;
            }
        }
        Ok(())
    }
}
