pub mod default;
pub mod mfp;
pub mod observer;
use crate::utils::source::get_fn_name_byid;

use super::super::Analysis;
use crate::compat::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Local, Place, StatementKind},
    ty::{GenericArgsRef, Ty, TyCtxt, TyKind},
};
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

    /// Return the intra-procedural local → origin mapping for a function.
    /// Default returns empty; analyser implementations may override with cached
    /// or MoP-based results.
    fn get_local_origins(&self, _def_id: DefId) -> LocalOriginMap {
        LocalOriginMap::default()
    }

    /// If a place (local + field projections) in a method body resolves to a
    /// struct's `self.field`, return the field identity.
    fn get_self_field_origin(
        &self,
        _def_id: DefId,
        _local: usize,
        _fields: &[usize],
    ) -> Option<FieldOrigin> {
        None
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

    /// Compress field paths: truncate each side's field list to its
    /// first element.  This matches the old MoP alias analysis behaviour
    /// where deeply nested fields like `0.0.0.0` are shortened to `0.0`.
    pub fn compress_fields(&mut self) {
        let alias_set = std::mem::take(&mut self.alias_set);
        let mut compressed = HashSet::with_capacity(alias_set.len());
        for mut ra in alias_set.into_iter() {
            if !ra.lhs_fields.is_empty() {
                ra.lhs_fields = vec![ra.lhs_fields[0]];
            }
            if !ra.rhs_fields.is_empty() {
                ra.rhs_fields = vec![ra.rhs_fields[0]];
            }
            compressed.insert(ra);
        }
        self.alias_set = compressed;
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
        writeln!(f, "=== Print alias analysis results ===")?;
        for (def_id, result) in &self.0 {
            let fn_name = get_fn_name_byid(def_id);
            writeln!(f, "Alias of {:?}: {}", fn_name, result)?;
        }
        Ok(())
    }
}

/// Lightweight intra-procedural local → origin mapping.
/// Maps `local_index` → `(origin_local_index, origin_field_projections)`.
pub type LocalOriginMap = FxHashMap<usize, (usize, Vec<usize>)>;

/// Identity of a struct field that a place resolves to.
#[derive(Clone, Debug)]
pub struct FieldOrigin {
    pub struct_def_id: DefId,
    pub field_index: usize,
    pub field_name: String,
}

/// Unwrap Ref / RawPtr / Adt layers to get the innermost ADT definition.
pub fn adt_from_ty<'tcx>(ty: Ty<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    match ty.kind() {
        TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => adt_from_ty(*inner),
        TyKind::Adt(adt, args) => Some((adt.did(), *args)),
        _ => None,
    }
}

/// Build a lightweight intra-procedural origin map by scanning MIR assignments.
/// For each `local = rvalue`, records the source place if the rvalue is a
/// simple copy / move / cast / ref / raw-ptr / copy-for-deref.
pub fn collect_local_origins<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> LocalOriginMap {
    let body = tcx.optimized_mir(def_id);
    let mut origins = LocalOriginMap::default();

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if let Some(origin) = rvalue_origin(rvalue, &origins) {
                origins.insert(target.local.as_usize(), origin);
            }
        }
        if let rustc_middle::mir::TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &block.terminator().kind
        {
            if let rustc_middle::mir::Operand::Constant(c) = func {
                if let rustc_middle::ty::FnDef(_, _) = c.const_.ty().kind() {
                    if let Some(first_arg) = args.first() {
                        if let Some(place) = first_arg.node.place() {
                            let origin = resolve_place(&place, &origins);
                            origins.insert(destination.local.as_usize(), origin);
                        }
                    }
                }
            }
        }
    }
    origins
}

/// Extract the origin `(local_index, fields)` from a rvalue, chasing through `origins`.
fn rvalue_origin(
    rvalue: &rustc_middle::mir::Rvalue<'_>,
    origins: &LocalOriginMap,
) -> Option<(usize, Vec<usize>)> {
    if let Some(place) = crate::helpers::mir_utils::rvalue_source_place(rvalue) {
        return Some(resolve_place(place, origins));
    }
    if let rustc_middle::mir::Rvalue::Cast(_, operand, _) = rvalue {
        if let Some(place) = operand.place() {
            return Some(resolve_place(&place, origins));
        }
    }
    None
}

/// Resolve a MIR Place through the origin map.
/// If the place has field projections, returns them directly.
/// Otherwise, follows the alias chain one level.
pub fn resolve_place(place: &Place<'_>, origins: &LocalOriginMap) -> (usize, Vec<usize>) {
    let local = place.local.as_usize();
    let fields: Vec<usize> = place
        .projection
        .iter()
        .filter_map(|elem| match elem {
            rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
            _ => None,
        })
        .collect();
    if !fields.is_empty() {
        return (local, fields);
    }
    origins.get(&local).cloned().unwrap_or((local, fields))
}

/// If `local` (typically `1` = self) with `fields` in `def_id`'s body
/// corresponds to a struct field, return its identity.
pub fn resolve_self_field_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    local: usize,
    fields: &[usize],
) -> Option<FieldOrigin> {
    if local != 1 || fields.is_empty() {
        return None;
    }
    let body = tcx.optimized_mir(def_id);
    let self_ty = body.local_decls[Local::from_usize(1)].ty;
    let (struct_def_id, _) = adt_from_ty(self_ty)?;
    let field_index = fields[0];
    let adt = tcx.adt_def(struct_def_id);
    let field = adt.all_fields().nth(field_index)?;
    Some(FieldOrigin {
        struct_def_id,
        field_index,
        field_name: field.name.to_string(),
    })
}

/// Like `resolve_self_field_origin` but uses the type of `local` instead
/// of always `_1`.  For origins from call-site verification.
pub fn resolve_any_field_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    local: usize,
    fields: &[usize],
) -> Option<FieldOrigin> {
    if fields.is_empty() {
        return None;
    }
    let body = tcx.optimized_mir(def_id);
    let self_ty = body.local_decls[Local::from_usize(local)].ty;
    let (struct_def_id, _) = adt_from_ty(self_ty)?;
    let field_index = fields[0];
    let adt = tcx.adt_def(struct_def_id);
    let field = adt.all_fields().nth(field_index)?;
    Some(FieldOrigin {
        struct_def_id,
        field_index,
        field_name: field.name.to_string(),
    })
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
