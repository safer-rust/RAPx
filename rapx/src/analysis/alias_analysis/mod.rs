pub mod default;
pub mod mfp;
use crate::utils::source::get_fn_name_byid;

use super::super::Analysis;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_span::def_id::LOCAL_CRATE;
use std::{collections::HashSet, fmt};

/// The data structure to store aliases for a set of functions.
pub type FnAliasMap = FxHashMap<DefId, FnAliasPairs>;

/// This is a wrapper struct for displaying FnAliasMap.
pub struct FnAliasMapWrapper(pub FnAliasMap);

/// This trait provides features related to alias analysis.
pub trait AliasAnalysis: Analysis {
    /// Return the aliases among the function arguments and return value of a specific function.
    fn get_fn_alias(&self, def_id: DefId) -> Option<FnAliasPairs>;
    /// Return the aliases among the function arguments and return value for all functions.
    fn get_all_fn_alias(&self) -> FnAliasMap;
    /// Return the aliases among the function arguments and return value for functions of the local
    /// crate.
    fn get_local_fn_alias(&self) -> FnAliasMap {
        self.get_all_fn_alias()
            .iter()
            .filter(|(def_id, _)| def_id.krate == LOCAL_CRATE)
            .map(|(k, v)| (*k, v.clone()))
            .collect()
    }
}

/// To store the alias relationships among arguments and return values.
/// Each function may have multiple return instructions, leading to different RetAlias.
#[derive(Debug, Clone)]
pub struct FnAliasPairs {
    arg_size: usize,
    alias_set: HashSet<AliasPair>,
}

impl FnAliasPairs {
    pub fn new(arg_size: usize) -> FnAliasPairs {
        Self {
            arg_size,
            alias_set: HashSet::new(),
        }
    }

    pub fn arg_size(&self) -> usize {
        self.arg_size
    }

    pub fn aliases(&self) -> &HashSet<AliasPair> {
        &self.alias_set
    }

    pub fn add_alias(&mut self, alias: AliasPair) {
        self.alias_set.insert(alias);
    }

    pub fn len(&self) -> usize {
        self.alias_set.len()
    }

    pub fn sort_alias_index(&mut self) {
        let alias_set = std::mem::take(&mut self.alias_set);
        let mut new_alias_set = HashSet::with_capacity(alias_set.len());

        for mut ra in alias_set.into_iter() {
            if ra.left_local() >= ra.right_local() {
                ra.swap();
            }
            new_alias_set.insert(ra);
        }
        self.alias_set = new_alias_set;
    }
}

impl fmt::Display for FnAliasPairs {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.aliases().is_empty() {
            write!(f, "null")?;
        } else {
            let mut facts: Vec<_> = self.aliases().iter().collect();
            facts.sort_by(|a, b| {
                a.left_local
                    .cmp(&b.left_local)
                    .then(a.right_local.cmp(&b.right_local))
                    .then(a.lhs_fields.cmp(&b.lhs_fields))
                    .then(a.rhs_fields.cmp(&b.rhs_fields))
            });
            let joined = facts
                .into_iter()
                .map(|fact| format!("{}", fact))
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, "{}", joined)?;
        }
        Ok(())
    }
}

impl fmt::Display for FnAliasMapWrapper {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "=== Print alias analysis resuts ===")?;
        for (def_id, result) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Alias of {:?}: {}", fn_name, result)?;
        }
        Ok(())
    }
}

/// AliasPair is used to store the alias relationships between two places.
/// The result is field-sensitive.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct AliasPair {
    pub left_local: usize,
    pub lhs_fields: Vec<usize>,
    pub right_local: usize,
    pub rhs_fields: Vec<usize>,
}

impl AliasPair {
    pub fn new(left_local: usize, right_local: usize) -> AliasPair {
        AliasPair {
            left_local,
            lhs_fields: Vec::<usize>::new(),
            right_local,
            rhs_fields: Vec::<usize>::new(),
        }
    }

    /// Swap the two elements of an alias pair, i.e., left to right, and right to left.
    pub fn swap(&mut self) {
        std::mem::swap(&mut self.left_local, &mut self.right_local);
        std::mem::swap(&mut self.lhs_fields, &mut self.rhs_fields);
    }

    pub fn left_local(&self) -> usize {
        self.left_local
    }

    pub fn right_local(&self) -> usize {
        self.right_local
    }

    pub fn lhs_fields(&self) -> &[usize] {
        &self.lhs_fields
    }

    pub fn rhs_fields(&self) -> &[usize] {
        &self.rhs_fields
    }
}

impl fmt::Display for AliasPair {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({},{})",
            aa_place_desc_str(self.left_local, &self.lhs_fields, true),
            aa_place_desc_str(self.right_local, &self.rhs_fields, true)
        )
    }
}

fn aa_place_desc_str(no: usize, fields: &[usize], field_sensitive: bool) -> String {
    let mut result = String::new();
    result.push_str(&no.to_string());
    if !field_sensitive {
        return result;
    }
    for num in fields.iter() {
        result.push('.');
        result.push_str(&num.to_string());
    }
    result
}
