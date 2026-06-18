#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]
pub mod default;
pub mod domain;
use crate::{
    analysis::{
        Analysis,
        range_analysis::domain::domain::{ConstConvert, IntervalArithmetic},
    },
    utils::source::get_fn_name_byid,
};
use once_cell::sync::Lazy;
// use intervals::Closed;
use crate::compat::FxHashMap;
use rust_intervals::Interval;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BinOp, Place};

use std;
use std::{
    collections::HashMap,
    fmt::{self, Debug, Display},
};
pub type RAResult<'tcx, T> = HashMap<Place<'tcx>, Range<T>>;
pub type RAResultMap<'tcx, T> = FxHashMap<DefId, HashMap<Place<'tcx>, Range<T>>>;
pub type RAVecResultMap<'tcx, T> = FxHashMap<DefId, Vec<HashMap<Place<'tcx>, Range<T>>>>;

pub type PathConstraint<'tcx> = HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>;
pub type PathConstraintMap<'tcx> =
    FxHashMap<DefId, HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>>>;
pub struct RAResultWrapper<'tcx, T: IntervalArithmetic>(pub RAResult<'tcx, T>);
pub struct RAResultMapWrapper<'tcx, T: IntervalArithmetic>(pub RAResultMap<'tcx, T>);
pub struct RAVecResultMapWrapper<'tcx, T: IntervalArithmetic>(pub RAVecResultMap<'tcx, T>);
pub struct PathConstraintWrapper<'tcx>(pub PathConstraint<'tcx>);
pub struct PathConstraintMapWrapper<'tcx>(pub PathConstraintMap<'tcx>);

/// The core trait for performing range analysis over Rust MIR.
///
/// This trait provides access to both intra-procedural and inter-procedural
/// range results inferred through static interval analysis.
pub trait RangeAnalysis<'tcx, T: IntervalArithmetic + ConstConvert + Debug>: Analysis {
    /// The fucntion returns the range information for all local variables (Places) in a given
    /// function specified by `def_id`.
    fn get_fn_range(&self, def_id: DefId) -> Option<RAResult<'tcx, T>>;

    /// The function returns the range analysis results for **each call instance** of the specified function.
    /// This is useful in interprocedural or context-sensitive analyses,
    /// where a function might be analyzed multiple times under different calling contexts.
    fn get_fn_ranges_percall(&self, def_id: DefId) -> Option<Vec<RAResult<'tcx, T>>>;

    /// The function returns the complete mapping of range information for all functions in the crate.
    fn get_all_fn_ranges(&self) -> RAResultMap<'tcx, T>;

    /// The function returns the range results for **every call instance** of every function in the crate.
    fn get_all_fn_ranges_percall(&self) -> RAVecResultMap<'tcx, T>;

    /// The function returns the inferred range for a specific variable (Place) in a specific function.
    fn get_fn_local_range(&self, def_id: DefId, local: Place<'tcx>) -> Option<Range<T>>;

    /// The function returns a mapping from feasible control-flow paths to symbolic constraints.
    /// Each constraint is a triple of (`Place`, `Place`, `BinOp`) representing
    /// path-sensitive relational information useful for pruning infeasible paths.
    fn get_fn_path_constraints(&self, def_id: DefId) -> Option<PathConstraint<'tcx>>;

    /// The function returns path constraints for all functions in the crate.
    fn get_all_path_constraints(&self) -> PathConstraintMap<'tcx>;
}

impl<'tcx, T> Display for RAResultWrapper<'tcx, T>
where
    Place<'tcx>: Debug,
    T: IntervalArithmetic + Clone + PartialOrd + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (place, range) in &self.0 {
            writeln!(f, "{:?} => {}", place, range)?;
        }
        Ok(())
    }
}
impl<'tcx, T> Display for RAResultMapWrapper<'tcx, T>
where
    DefId: Debug,
    Place<'tcx>: Debug,
    T: IntervalArithmetic + Clone + PartialOrd + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print range analysis results ===")?;
        for (def_id, ra_result) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Function: {:?} =>", fn_name)?;

            let mut sorted: Vec<_> = ra_result.iter().collect();
            sorted.sort_by_key(|(place, _)| place.local.as_usize());

            for (place, range) in sorted {
                writeln!(f, "  {:?} => {}", place, range)?;
            }
        }
        Ok(())
    }
}
impl<'tcx, T> Display for RAVecResultMapWrapper<'tcx, T>
where
    DefId: Debug,
    Place<'tcx>: Debug,
    T: IntervalArithmetic + Clone + PartialOrd + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print range analysis resuts ===")?;
        for (def_id, vec_of_maps) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Function: {:?} =>", fn_name)?;

            for (i, map) in vec_of_maps.iter().enumerate() {
                writeln!(f, "  Result Set #{}:", i)?;

                let mut sorted: Vec<_> = map.iter().collect();
                sorted.sort_by_key(|(place, _)| place.local.as_usize());

                for (place, range) in sorted {
                    writeln!(f, "    {:?} => {}", place, range)?;
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> Display for PathConstraintWrapper<'tcx>
where
    Place<'tcx>: Debug,
    BinOp: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (path, constraints) in &self.0 {
            writeln!(f, "Path {:?}:", path)?;
            for (p1, p2, op) in constraints {
                writeln!(f, "    Constraint:{:?} {:?} {:?}", p1, op, p2)?;
            }
        }
        Ok(())
    }
}

impl<'tcx> Display for PathConstraintMapWrapper<'tcx>
where
    DefId: Debug,
    Place<'tcx>: Debug,
    BinOp: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print paths and constraints ===")?;
        for (def_id, pc) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Function: {:?}:", fn_name)?;
            for (path, constraints) in pc {
                writeln!(f, "  Path {:?}:", path)?;
                for (p1, p2, op) in constraints {
                    writeln!(f, "    Constraint:{:?} {:?} {:?}", p1, op, p2)?;
                }
            }
        }
        Ok(())
    }
}
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum RangeType {
    Unknown,
    Regular,
    Empty,
}
impl fmt::Display for RangeType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            RangeType::Unknown => "Unknown",
            RangeType::Regular => "Regular",
            RangeType::Empty => "Empty",
        };
        write!(f, "{}", s)
    }
}

#[derive(Debug, Hash, Clone, PartialEq, Eq)]

pub struct Range<T>
where
    T: IntervalArithmetic,
{
    pub rtype: RangeType,
    pub range: Interval<T>,
}
static STR_MIN: Lazy<String> = Lazy::new(|| "Min".to_string());
static STR_MAX: Lazy<String> = Lazy::new(|| "Max".to_string());
impl<T> Display for Range<T>
where
    T: IntervalArithmetic + std::fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let lower: String = if *self.range.lower().unwrap() == T::min_value() {
            STR_MIN.clone()
        } else if *self.range.lower().unwrap() == T::max_value() {
            STR_MAX.clone()
        } else {
            self.range.lower().unwrap().to_string()
        };

        let upper: String = if *self.range.upper().unwrap() == T::min_value() {
            STR_MIN.clone()
        } else if *self.range.upper().unwrap() == T::max_value() {
            STR_MAX.clone()
        } else {
            self.range.upper().unwrap().to_string()
        };

        write!(f, "{:?} [{}, {}]", self.rtype, lower, upper)
    }
}
