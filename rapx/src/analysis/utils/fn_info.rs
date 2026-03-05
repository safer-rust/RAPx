use super::draw_dot::render_dot_string;
use crate::analysis::{
    core::dataflow::{DataFlowAnalysis, default::DataFlowAnalyzer},
    senryx::{
        contracts::property::{self, PropertyContract},
        matcher::parse_unsafe_api,
    },
    utils::draw_dot::DotGraph,
};
use crate::def_id::*;
use crate::{rap_debug, rap_warn};
use rustc_ast::ItemKind;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::{
    Attribute, ImplItemKind, Safety,
    def::DefKind,
    def_id::{CrateNum, DefId, DefIndex},
};
use rustc_middle::{
    hir::place::PlaceBase,
    mir::{
        BasicBlock, BinOp, Body, Local, Operand, Place, PlaceElem, PlaceRef, ProjectionElem,
        Rvalue, StatementKind, Terminator, TerminatorKind,
    },
    ty,
    ty::{AssocKind, ConstKind, Mutability, Ty, TyCtxt, TyKind},
};
use rustc_span::{def_id::LocalDefId, kw, sym};
use serde::de;
use serde::{Deserialize, Serialize};
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};
use syn::Expr;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum FnKind {
    Fn,
    Method,
    Constructor,
    Intrinsic,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FnInfo {
    pub def_id: DefId,
    pub fn_safety: Safety,
    pub fn_kind: FnKind,
}

impl FnInfo {
    pub fn new(def_id: DefId, fn_safety: Safety, fn_kind: FnKind) -> Self {
        FnInfo {
            def_id,
            fn_safety,
            fn_kind,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AdtInfo {
    pub def_id: DefId,
    pub literal_cons_enabled: bool,
}

impl AdtInfo {
    pub fn new(def_id: DefId, literal_cons_enabled: bool) -> Self {
        AdtInfo {
            def_id,
            literal_cons_enabled,
        }
    }
}

pub fn check_visibility(tcx: TyCtxt, func_defid: DefId) -> bool {
    if !tcx.visibility(func_defid).is_public() {
        return false;
    }
    true
}

pub fn is_re_exported(tcx: TyCtxt, target_defid: DefId, module_defid: LocalDefId) -> bool {
    for child in tcx.module_children_local(module_defid) {
        if child.vis.is_public() {
            if let Some(def_id) = child.res.opt_def_id() {
                if def_id == target_defid {
                    return true;
                }
            }
        }
    }
    false
}

pub fn print_hashset<T: std::fmt::Debug>(set: &HashSet<T>) {
    for item in set {
        println!("{:?}", item);
    }
    println!("---------------");
}

pub fn get_cleaned_def_path_name_ori(tcx: TyCtxt, def_id: DefId) -> String {
    let def_id_str = format!("{:?}", def_id);
    let mut parts: Vec<&str> = def_id_str.split("::").collect();

    let mut remove_first = false;
    if let Some(first_part) = parts.get_mut(0) {
        if first_part.contains("core") {
            *first_part = "core";
        } else if first_part.contains("std") {
            *first_part = "std";
        } else if first_part.contains("alloc") {
            *first_part = "alloc";
        } else {
            remove_first = true;
        }
    }
    if remove_first && !parts.is_empty() {
        parts.remove(0);
    }

    let new_parts: Vec<String> = parts
        .into_iter()
        .filter_map(|s| {
            if s.contains("{") {
                if remove_first {
                    get_struct_name(tcx, def_id)
                } else {
                    None
                }
            } else {
                Some(s.to_string())
            }
        })
        .collect();

    let mut cleaned_path = new_parts.join("::");
    cleaned_path = cleaned_path.trim_end_matches(')').to_string();
    cleaned_path
}

pub fn get_sp_tags_json() -> serde_json::Value {
    let json_data: serde_json::Value =
        serde_json::from_str(include_str!("assets/std_sps.json")).expect("Unable to parse JSON");
    json_data
}

pub fn get_std_api_signature_json() -> serde_json::Value {
    let json_data: serde_json::Value =
        serde_json::from_str(include_str!("assets/std_sig.json")).expect("Unable to parse JSON");
    json_data
}

pub fn get_sp_tags_and_args_json() -> serde_json::Value {
    let json_data: serde_json::Value =
        serde_json::from_str(include_str!("assets/std_sps_args.json"))
            .expect("Unable to parse JSON");
    json_data
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ContractEntry {
    pub tag: String,
    pub args: Vec<String>,
}

pub fn get_std_contracts(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<ContractEntry> {
    let cleaned_path_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data: serde_json::Value = get_sp_tags_and_args_json();

    if let Some(entries) = json_data.get(&cleaned_path_name) {
        if let Ok(contracts) = serde_json::from_value::<Vec<ContractEntry>>(entries.clone()) {
            return contracts;
        }
    }
    Vec::new()
}

pub fn get_sp(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<String> {
    let cleaned_path_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data: serde_json::Value = get_sp_tags_json();

    if let Some(function_info) = json_data.get(&cleaned_path_name) {
        if let Some(sp_list) = function_info.get("0") {
            let mut result = HashSet::new();
            if let Some(sp_array) = sp_list.as_array() {
                for sp in sp_array {
                    if let Some(sp_name) = sp.as_str() {
                        result.insert(sp_name.to_string());
                    }
                }
            }
            return result;
        }
    }
    HashSet::new()
}

pub fn get_struct_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            let ty = tcx.type_of(impl_id).skip_binder();
            let type_name = ty.to_string();
            let struct_name = type_name
                .split('<')
                .next()
                .unwrap_or("")
                .split("::")
                .last()
                .unwrap_or("")
                .to_string();

            return Some(struct_name);
        }
    }
    None
}

pub fn check_safety(tcx: TyCtxt<'_>, def_id: DefId) -> Safety {
    let poly_fn_sig = tcx.fn_sig(def_id);
    let fn_sig = poly_fn_sig.skip_binder();
    fn_sig.safety()
}

pub fn get_type(tcx: TyCtxt<'_>, def_id: DefId) -> FnKind {
    let mut node_type = 2;
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        match assoc_item.kind {
            AssocKind::Fn { has_self, .. } => {
                if has_self {
                    return FnKind::Method;
                } else {
                    let fn_sig = tcx.fn_sig(def_id).skip_binder();
                    let output = fn_sig.output().skip_binder();
                    // return type is 'Self'
                    if output.is_param(0) {
                        return FnKind::Constructor;
                    }
                    // return type is struct's name
                    if let Some(impl_id) = assoc_item.impl_container(tcx) {
                        let ty = tcx.type_of(impl_id).skip_binder();
                        if output == ty {
                            return FnKind::Constructor;
                        }
                    }
                    match output.kind() {
                        TyKind::Ref(_, ref_ty, _) => {
                            if ref_ty.is_param(0) {
                                return FnKind::Constructor;
                            }
                            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                                let ty = tcx.type_of(impl_id).skip_binder();
                                if *ref_ty == ty {
                                    return FnKind::Constructor;
                                }
                            }
                        }
                        TyKind::Adt(adt_def, substs) => {
                            if adt_def.is_enum()
                                && (tcx.is_diagnostic_item(sym::Option, adt_def.did())
                                    || tcx.is_diagnostic_item(sym::Result, adt_def.did())
                                    || tcx.is_diagnostic_item(kw::Box, adt_def.did()))
                            {
                                let inner_ty = substs.type_at(0);
                                if inner_ty.is_param(0) {
                                    return FnKind::Constructor;
                                }
                                if let Some(impl_id) = assoc_item.impl_container(tcx) {
                                    let ty_impl = tcx.type_of(impl_id).skip_binder();
                                    if inner_ty == ty_impl {
                                        return FnKind::Constructor;
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => todo!(),
        }
    }
    return FnKind::Fn;
}

pub fn get_adt_ty(tcx: TyCtxt, def_id: DefId) -> Option<Ty> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            return Some(tcx.type_of(impl_id).skip_binder());
        }
    }
    None
}

// check whether this adt contains a literal constructor
// result: adt_def_id, is_literal
pub fn get_adt_via_method(tcx: TyCtxt<'_>, method_def_id: DefId) -> Option<AdtInfo> {
    let assoc_item = tcx.opt_associated_item(method_def_id)?;
    let impl_id = assoc_item.impl_container(tcx)?;
    let ty = tcx.type_of(impl_id).skip_binder();
    let adt_def = ty.ty_adt_def()?;
    let adt_def_id = adt_def.did();

    let all_fields: Vec<_> = adt_def.all_fields().collect();
    let total_count = all_fields.len();

    if total_count == 0 {
        return Some(AdtInfo::new(adt_def_id, true));
    }

    let pub_count = all_fields
        .iter()
        .filter(|field| tcx.visibility(field.did).is_public())
        .count();

    if pub_count == 0 {
        return None;
    }
    Some(AdtInfo::new(adt_def_id, pub_count == total_count))
}

fn place_has_raw_deref<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: &Place<'tcx>) -> bool {
    let mut local = place.local;
    for proj in place.projection.iter() {
        if let ProjectionElem::Deref = proj.kind() {
            let ty = body.local_decls[local].ty;
            if let TyKind::RawPtr(_, _) = ty.kind() {
                return true;
            }
        }
    }
    false
}

/// Analyzes the MIR of the given function to collect all local variables
/// that are involved in dereferencing raw pointers (`*const T` or `*mut T`).
pub fn get_rawptr_deref(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<Local> {
    let mut raw_ptrs = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind {
                    if place_has_raw_deref(tcx, &body, lhs) {
                        raw_ptrs.insert(lhs.local);
                    }
                    if let Rvalue::Use(op) = rhs {
                        match op {
                            Operand::Copy(place) | Operand::Move(place) => {
                                if place_has_raw_deref(tcx, &body, place) {
                                    raw_ptrs.insert(place.local);
                                }
                            }
                            _ => {}
                        }
                    }
                    if let Rvalue::Ref(_, _, place) = rhs {
                        if place_has_raw_deref(tcx, &body, place) {
                            raw_ptrs.insert(place.local);
                        }
                    }
                }
            }
            if let Some(terminator) = &bb.terminator {
                match &terminator.kind {
                    rustc_middle::mir::TerminatorKind::Call { args, .. } => {
                        for arg in args {
                            match arg.node {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    if place_has_raw_deref(tcx, &body, &place) {
                                        raw_ptrs.insert(place.local);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    raw_ptrs
}

/* Example mir of static mutable access.

static mut COUNTER: i32 = {
    let mut _0: i32;

    bb0: {
        _0 = const 0_i32;
        return;
    }
}

fn main() -> () {
    let mut _0: ();
    let mut _1: *mut i32;

    bb0: {
        StorageLive(_1);
        _1 = const {alloc1: *mut i32};
        (*_1) = const 1_i32;
        StorageDead(_1);
        return;
    }
}

alloc1 (static: COUNTER, size: 4, align: 4) {
    00 00 00 00                                     │ ....
}

*/

/// Collects pairs of global static variables and their corresponding local variables
/// within a function's MIR that are assigned from statics.
pub fn collect_global_local_pairs(tcx: TyCtxt<'_>, def_id: DefId) -> HashMap<DefId, Vec<Local>> {
    let mut globals: HashMap<DefId, Vec<Local>> = HashMap::new();

    if !tcx.is_mir_available(def_id) {
        return globals;
    }

    let body = tcx.optimized_mir(def_id);

    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            if let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind {
                if let Rvalue::Use(Operand::Constant(c)) = rhs {
                    if let Some(static_def_id) = c.check_static_ptr(tcx) {
                        globals.entry(static_def_id).or_default().push(lhs.local);
                    }
                }
            }
        }
    }

    globals
}

pub fn get_unsafe_callees(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<DefId> {
    let mut unsafe_callees = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                        if check_safety(tcx, *callee_def_id) == Safety::Unsafe {
                            unsafe_callees.insert(*callee_def_id);
                        }
                    }
                }
            }
        }
    }
    unsafe_callees
}

pub fn get_all_callees(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<DefId> {
    let mut callees = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                        callees.insert(*callee_def_id);
                    }
                }
            }
        }
    }
    callees
}

// return all the impls def id of corresponding struct
pub fn get_impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        if let rustc_hir::ItemKind::Impl(impl_details) = &item.kind {
            if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                &impl_details.self_ty.kind
            {
                if let rustc_hir::def::Res::Def(_, def_id) = path.res {
                    if def_id == struct_def_id {
                        impls.push(item_id.owner_id.to_def_id());
                    }
                }
            }
        }
    }
    impls
}

pub fn get_adt_def_id_by_adt_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            // get struct ty
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                return Some(adt_def.did());
            }
        }
    }
    None
}

// get the pointee or wrapped type
pub fn get_pointee(matched_ty: Ty<'_>) -> Ty<'_> {
    // progress_info!("get_pointee: > {:?} as type: {:?}", matched_ty, matched_ty.kind());
    let pointee = if let ty::RawPtr(ty_mut, _) = matched_ty.kind() {
        get_pointee(*ty_mut)
    } else if let ty::Ref(_, referred_ty, _) = matched_ty.kind() {
        get_pointee(*referred_ty)
    } else {
        matched_ty
    };
    pointee
}

pub fn is_ptr(matched_ty: Ty<'_>) -> bool {
    if let ty::RawPtr(_, _) = matched_ty.kind() {
        return true;
    }
    false
}

pub fn is_ref(matched_ty: Ty<'_>) -> bool {
    if let ty::Ref(_, _, _) = matched_ty.kind() {
        return true;
    }
    false
}

pub fn is_slice(matched_ty: Ty) -> Option<Ty> {
    if let ty::Slice(inner) = matched_ty.kind() {
        return Some(*inner);
    }
    None
}

pub fn has_mut_self_param(tcx: TyCtxt, def_id: DefId) -> bool {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        match assoc_item.kind {
            AssocKind::Fn { has_self, .. } => {
                if has_self && tcx.is_mir_available(def_id) {
                    let body = tcx.optimized_mir(def_id);
                    let fst_arg = body.local_decls[Local::from_usize(1)].clone();
                    let ty = fst_arg.ty;
                    let is_mut_ref =
                        matches!(ty.kind(), ty::Ref(_, _, mutbl) if *mutbl == Mutability::Mut);
                    return fst_arg.mutability.is_mut() || is_mut_ref;
                }
            }
            _ => (),
        }
    }
    false
}

// Check each field's visibility, return the public fields vec
pub fn get_public_fields(tcx: TyCtxt, def_id: DefId) -> HashSet<usize> {
    let adt_def = tcx.adt_def(def_id);
    adt_def
        .all_fields()
        .enumerate()
        .filter_map(|(index, field_def)| tcx.visibility(field_def.did).is_public().then_some(index))
        .collect()
}

// general function for displaying hashmap
pub fn display_hashmap<K, V>(map: &HashMap<K, V>, level: usize)
where
    K: Ord + Debug + Hash,
    V: Debug,
{
    let indent = "  ".repeat(level);
    let mut sorted_keys: Vec<_> = map.keys().collect();
    sorted_keys.sort();

    for key in sorted_keys {
        if let Some(value) = map.get(key) {
            println!("{}{:?}: {:?}", indent, key, value);
        }
    }
}

pub fn match_std_unsafe_chains_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Vec<String> {
    let mut results = Vec::new();
    if let TerminatorKind::Call { func, .. } = &terminator.kind {
        if let Operand::Constant(func_constant) = func {
            if let ty::FnDef(callee_def_id, _raw_list) = func_constant.const_.ty().kind() {
                let func_name = get_cleaned_def_path_name(tcx, *callee_def_id);
            }
        }
    }
    results
}

pub fn get_all_std_unsafe_callees(tcx: TyCtxt, def_id: DefId) -> Vec<String> {
    let mut results = Vec::new();
    let body = tcx.optimized_mir(def_id);
    let bb_len = body.basic_blocks.len();
    for i in 0..bb_len {
        let callees = match_std_unsafe_callee(
            tcx,
            body.basic_blocks[BasicBlock::from_usize(i)]
                .clone()
                .terminator(),
        );
        results.extend(callees);
    }
    results
}

pub fn get_all_std_unsafe_callees_block_id(tcx: TyCtxt, def_id: DefId) -> Vec<usize> {
    let mut results = Vec::new();
    let body = tcx.optimized_mir(def_id);
    let bb_len = body.basic_blocks.len();
    for i in 0..bb_len {
        if match_std_unsafe_callee(
            tcx,
            body.basic_blocks[BasicBlock::from_usize(i)]
                .clone()
                .terminator(),
        )
        .is_empty()
        {
            results.push(i);
        }
    }
    results
}

pub fn match_std_unsafe_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Vec<String> {
    let mut results = Vec::new();
    if let TerminatorKind::Call { func, .. } = &terminator.kind {
        if let Operand::Constant(func_constant) = func {
            if let ty::FnDef(callee_def_id, _raw_list) = func_constant.const_.ty().kind() {
                let func_name = get_cleaned_def_path_name(tcx, *callee_def_id);
                // rap_info!("{func_name}");
                if parse_unsafe_api(&func_name).is_some() {
                    results.push(func_name);
                }
            }
        }
    }
    results
}

// Bug definition: (1) strict -> weak & dst is mutable;
//                 (2) _ -> strict
pub fn is_strict_ty_convert<'tcx>(tcx: TyCtxt<'tcx>, src_ty: Ty<'tcx>, dst_ty: Ty<'tcx>) -> bool {
    (is_strict_ty(tcx, src_ty) && dst_ty.is_mutable_ptr()) || is_strict_ty(tcx, dst_ty)
}

// strict ty: bool, str, adt fields containing bool or str;
pub fn is_strict_ty<'tcx>(tcx: TyCtxt<'tcx>, ori_ty: Ty<'tcx>) -> bool {
    let ty = get_pointee(ori_ty);
    let mut flag = false;
    if let TyKind::Adt(adt_def, substs) = ty.kind() {
        if adt_def.is_struct() {
            for field_def in adt_def.all_fields() {
                flag |= is_strict_ty(tcx, field_def.ty(tcx, substs))
            }
        }
    }
    ty.is_bool() || ty.is_str() || flag
}

pub fn reverse_op(op: BinOp) -> BinOp {
    match op {
        BinOp::Lt => BinOp::Ge,
        BinOp::Ge => BinOp::Lt,
        BinOp::Le => BinOp::Gt,
        BinOp::Gt => BinOp::Le,
        BinOp::Eq => BinOp::Eq,
        BinOp::Ne => BinOp::Ne,
        _ => op,
    }
}

/// Generate contracts from pre-defined std-lib JSON configuration (std_sps_args.json).
pub fn generate_contract_from_std_annotation_json(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> Vec<(usize, Vec<usize>, PropertyContract<'_>)> {
    let mut results = Vec::new();
    let std_contracts = get_std_contracts(tcx, def_id);

    for entry in std_contracts {
        let tag_name = entry.tag;
        let raw_args = entry.args;

        if raw_args.is_empty() {
            continue;
        }

        let arg_index_str = &raw_args[0];
        let local_id = if let Ok(arg_idx) = arg_index_str.parse::<usize>() {
            arg_idx
        } else {
            rap_error!(
                "JSON Contract Error: First argument must be an arg index number, got {}",
                arg_index_str
            );
            continue;
        };

        let mut exprs: Vec<Expr> = Vec::new();
        for arg_str in &raw_args {
            match syn::parse_str::<Expr>(arg_str) {
                Ok(expr) => exprs.push(expr),
                Err(_) => {
                    rap_error!(
                        "JSON Contract Error: Failed to parse arg '{}' as Rust Expr for tag {}",
                        arg_str,
                        tag_name
                    );
                }
            }
        }

        // Robustness check of arguments transition
        if exprs.len() != raw_args.len() {
            rap_error!(
                "Parse std API args error: Failed to parse arg '{:?}'",
                raw_args
            );
            continue;
        }
        let fields: Vec<usize> = Vec::new();
        let contract = PropertyContract::new(tcx, def_id, &tag_name, &exprs);
        results.push((local_id, fields, contract));
    }

    // rap_warn!("Get contract {:?}.", results);
    results
}

/// Same with `generate_contract_from_annotation` but does not contain field types.
pub fn generate_contract_from_annotation_without_field_types(
    tcx: TyCtxt,
    def_id: DefId,
) -> Vec<(usize, Vec<usize>, PropertyContract)> {
    let contracts_with_ty = generate_contract_from_annotation(tcx, def_id);

    contracts_with_ty
        .into_iter()
        .map(|(local_id, fields_with_ty, contract)| {
            let fields: Vec<usize> = fields_with_ty
                .into_iter()
                .map(|(field_idx, _)| field_idx)
                .collect();
            (local_id, fields, contract)
        })
        .collect()
}

/// Filter the function which contains "rapx::proof"
pub fn is_verify_target_func(tcx: TyCtxt, def_id: DefId) -> bool {
    for attr in tcx.get_all_attrs(def_id).into_iter() {
        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
        // Find proof placeholder
        if attr_str.contains("#[rapx::proof(proof)]") {
            return true;
        }
    }
    false
}

/// Get the annotation in tag-std style.
/// Then generate the contractual invariant states (CIS) for the args.
/// This function will recognize the args name and record states to MIR variable (represent by usize).
/// Return value means Vec<(local_id, fields of this local, contracts)>
pub fn generate_contract_from_annotation(
    tcx: TyCtxt,
    def_id: DefId,
) -> Vec<(usize, Vec<(usize, Ty)>, PropertyContract)> {
    const REGISTER_TOOL: &str = "rapx";
    let tool_attrs = tcx.get_all_attrs(def_id).into_iter().filter(|attr| {
        if let Attribute::Unparsed(tool_attr) = attr {
            if tool_attr.path.segments[0].as_str() == REGISTER_TOOL {
                return true;
            }
        }
        false
    });
    let mut results = Vec::new();
    for attr in tool_attrs {
        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
        // Find proof placeholder, skip it
        if attr_str.contains("#[rapx::proof(proof)]") {
            continue;
        }
        rap_debug!("{:?}", attr_str);
        let safety_attr = safety_parser::safety::parse_attr_and_get_properties(attr_str.as_str());
        for par in safety_attr.iter() {
            for property in par.tags.iter() {
                let tag_name = property.tag.name();
                let exprs = property.args.clone().into_vec();
                let contract = PropertyContract::new(tcx, def_id, tag_name, &exprs);
                let (local, fields) = parse_cis_local(tcx, def_id, exprs);
                results.push((local, fields, contract));
            }
        }
    }
    // if results.len() > 0 {
    //     rap_warn!("results:\n{:?}", results);
    // }
    results
}

/// Parse attr.expr into local id and local fields.
///
/// Example:
/// ```
/// #[rapx::inner(property = ValidPtr(ptr, u32, 1), kind = "precond")]
/// #[rapx::inner(property = ValidNum(region.size>=0), kind = "precond")]
/// pub fn xor_secret_region(ptr: *mut u32, region:SecretRegion) -> u32 {...}
/// ```
///
/// The first attribute will be parsed as (1, []).
///     -> "1" means the first arg "ptr", "[]" means no fields.
/// The second attribute will be parsed as (2, [1]).
///     -> "2" means the second arg "region", "[1]" means "size" is region's second field.
///
/// If this function doesn't have args, then it will return default pattern: (0, Vec::new())
pub fn parse_cis_local(tcx: TyCtxt, def_id: DefId, expr: Vec<Expr>) -> (usize, Vec<(usize, Ty)>) {
    // match expr with cis local
    for e in expr {
        if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, &e) {
            return (base, fields);
        }
    }
    (0, Vec::new())
}

/// parse single expr into (local, fields, ty)
pub fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(&expr) {
        let (param_names, param_tys) = parse_signature(tcx, def_id);
        if param_names[0] == "0".to_string() {
            return None;
        }
        if let Some(param_index) = param_names.iter().position(|name| name == &base_ident) {
            let mut current_ty = param_tys[param_index];
            let mut field_indices = Vec::new();
            for field_name in fields {
                // peel the ref and ptr
                let peeled_ty = current_ty.peel_refs();
                if let rustc_middle::ty::TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
                    let variant = adt_def.non_enum_variant();
                    // 1. if field_name is number, then parse it as usize
                    if let Ok(field_idx) = field_name.parse::<usize>() {
                        if field_idx < variant.fields.len() {
                            current_ty = variant.fields[rustc_abi::FieldIdx::from_usize(field_idx)]
                                .ty(tcx, arg_list);
                            field_indices.push((field_idx, current_ty));
                            continue;
                        }
                    }
                    // 2. if field_name is String, then compare it with current ty's field names
                    if let Some((idx, _)) = variant
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, f)| f.ident(tcx).name.to_string() == field_name.clone())
                    {
                        current_ty =
                            variant.fields[rustc_abi::FieldIdx::from_usize(idx)].ty(tcx, arg_list);
                        field_indices.push((idx, current_ty));
                    }
                    // 3. if field_name can not match any fields, then break
                    else {
                        break; // TODO:
                    }
                }
                // if current ty is not Adt, then break the loop
                else {
                    break; // TODO:
                }
            }
            // It's different from default one, we return the result as param_index+1 because param_index count from 0.
            // But 0 in MIR is the ret index, the args' indexes begin from 1.
            return Some((param_index + 1, field_indices, current_ty));
        }
    }
    None
}

/// Return the Vecs of args' names and types
/// This function will handle outside def_id by different way.
pub fn parse_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    // 0. If the def id is local
    if def_id.as_local().is_some() {
        return parse_local_signature(tcx, def_id);
    } else {
        rap_debug!("{:?} is not local def id.", def_id);
        return parse_outside_signature(tcx, def_id);
    };
}

/// Return the Vecs of args' names and types of outside functions.
fn parse_outside_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let sig = tcx.fn_sig(def_id).skip_binder();
    let param_tys: Vec<Ty<'tcx>> = sig.inputs().skip_binder().iter().copied().collect();

    // 1. check pre-defined std unsafe api signature
    if let Some(args_name) = get_known_std_names(tcx, def_id) {
        // rap_warn!(
        //     "function {:?} has arg: {:?}, arg types: {:?}",
        //     def_id,
        //     args_name,
        //     param_tys
        // );
        return (args_name, param_tys);
    }

    // 2. TODO: If can not find known std apis, then use numbers like `0`,`1`,... to represent args.
    let args_name = (0..param_tys.len()).map(|i| format!("{}", i)).collect();
    rap_debug!(
        "function {:?} has arg: {:?}, arg types: {:?}",
        def_id,
        args_name,
        param_tys
    );
    return (args_name, param_tys);
}

/// We use a json to record known std apis' arg names.
/// This function will search the json and return the names.
/// Notes: If std gets updated, the json may still record old ones.
fn get_known_std_names<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<String>> {
    let std_func_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data: serde_json::Value = get_std_api_signature_json();

    if let Some(arg_info) = json_data.get(&std_func_name) {
        if let Some(args_name) = arg_info.as_array() {
            // set default value to arg name
            if args_name.len() == 0 {
                return Some(vec!["0".to_string()]);
            }
            // iterate and collect
            let mut result = Vec::new();
            for arg in args_name {
                if let Some(sp_name) = arg.as_str() {
                    result.push(sp_name.to_string());
                }
            }
            return Some(result);
        }
    }
    None
}

/// Return the Vecs of args' names and types of local functions.
pub fn parse_local_signature(tcx: TyCtxt, def_id: DefId) -> (Vec<String>, Vec<Ty>) {
    // 1. parse local def_id and get arg list
    let local_def_id = def_id.as_local().unwrap();
    let hir_body = tcx.hir_body_owned_by(local_def_id);
    if hir_body.params.len() == 0 {
        return (vec!["0".to_string()], Vec::new());
    }
    // 2. contruct the vec of param and param ty
    let params = hir_body.params;
    let typeck_results = tcx.typeck_body(hir_body.id());
    let mut param_names = Vec::new();
    let mut param_tys = Vec::new();
    for param in params {
        match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => {
                param_names.push(ident.name.to_string());
                let ty = typeck_results.pat_ty(param.pat);
                param_tys.push(ty);
            }
            _ => {
                param_names.push(String::new());
                param_tys.push(typeck_results.pat_ty(param.pat));
            }
        }
    }
    (param_names, param_tys)
}

/// return the (ident, its fields) of the expr.
///
/// illustrated cases :
///    ptr	-> ("ptr", [])
///    region.size	-> ("region", ["size"])
///    tuple.0.value -> ("tuple", ["0", "value"])
pub fn access_ident_recursive(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Path(syn::ExprPath { path, .. }) => {
            if path.segments.len() == 1 {
                rap_debug!("expr2 {:?}", expr);
                let ident = path.segments[0].ident.to_string();
                Some((ident, Vec::new()))
            } else {
                None
            }
        }
        // get the base and fields recursively
        Expr::Field(syn::ExprField { base, member, .. }) => {
            let (base_ident, mut fields) =
                if let Some((base_ident, fields)) = access_ident_recursive(base) {
                    (base_ident, fields)
                } else {
                    return None;
                };
            let field_name = match member {
                syn::Member::Named(ident) => ident.to_string(),
                syn::Member::Unnamed(index) => index.index.to_string(),
            };
            fields.push(field_name);
            Some((base_ident, fields))
        }
        _ => None,
    }
}

/// parse expr into number.
pub fn parse_expr_into_number(expr: &Expr) -> Option<usize> {
    if let Expr::Lit(expr_lit) = expr {
        if let syn::Lit::Int(lit_int) = &expr_lit.lit {
            return lit_int.base10_parse::<usize>().ok();
        }
    }
    None
}

/// Match a type identifier string to a concrete Rust type
///
/// This function attempts to match a given type identifier (e.g., "u32", "T", "MyStruct")
/// to a type in the provided parameter type list. It handles:
/// 1. Built-in primitive types (u32, usize, etc.)
/// 2. Generic type parameters (T, U, etc.)
/// 3. User-defined types found in the parameter list
///
/// Arguments:
/// - `tcx`: Type context for querying compiler information
/// - `type_ident`: String representing the type identifier to match
/// - `param_ty`: List of parameter types from the function signature
///
/// Returns:
/// - `Some(Ty)` if a matching type is found
/// - `None` if no match is found
pub fn match_ty_with_ident(tcx: TyCtxt, def_id: DefId, type_ident: String) -> Option<Ty> {
    // 1. First check for built-in primitive types
    if let Some(primitive_ty) = match_primitive_type(tcx, type_ident.clone()) {
        return Some(primitive_ty);
    }
    // 2. Check if the identifier matches any generic type parameter
    return find_generic_param(tcx, def_id, type_ident.clone());
    // 3. Check if the identifier matches any user-defined type in the parameters
    // find_user_defined_type(tcx, def_id, type_ident)
}

/// Match built-in primitive types from String
fn match_primitive_type(tcx: TyCtxt, type_ident: String) -> Option<Ty> {
    match type_ident.as_str() {
        "i8" => Some(tcx.types.i8),
        "i16" => Some(tcx.types.i16),
        "i32" => Some(tcx.types.i32),
        "i64" => Some(tcx.types.i64),
        "i128" => Some(tcx.types.i128),
        "isize" => Some(tcx.types.isize),
        "u8" => Some(tcx.types.u8),
        "u16" => Some(tcx.types.u16),
        "u32" => Some(tcx.types.u32),
        "u64" => Some(tcx.types.u64),
        "u128" => Some(tcx.types.u128),
        "usize" => Some(tcx.types.usize),
        "f16" => Some(tcx.types.f16),
        "f32" => Some(tcx.types.f32),
        "f64" => Some(tcx.types.f64),
        "f128" => Some(tcx.types.f128),
        "bool" => Some(tcx.types.bool),
        "char" => Some(tcx.types.char),
        "str" => Some(tcx.types.str_),
        _ => None,
    }
}

/// Find generic type parameters in the parameter list
fn find_generic_param(tcx: TyCtxt, def_id: DefId, type_ident: String) -> Option<Ty> {
    rap_debug!(
        "Searching for generic param: {} in {:?}",
        type_ident,
        def_id
    );
    let (_, param_tys) = parse_signature(tcx, def_id);
    rap_debug!("Function parameter types: {:?} of {:?}", param_tys, def_id);
    // 递归查找泛型参数
    for &ty in &param_tys {
        if let Some(found) = find_generic_in_ty(tcx, ty, &type_ident) {
            return Some(found);
        }
    }

    None
}

/// Iterate the args' types recursively and find the matched generic one.
fn find_generic_in_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, type_ident: &str) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::Param(param_ty) => {
            if param_ty.name.as_str() == type_ident {
                return Some(ty);
            }
        }
        TyKind::RawPtr(ty, _)
        | TyKind::Ref(_, ty, _)
        | TyKind::Slice(ty)
        | TyKind::Array(ty, _) => {
            if let Some(found) = find_generic_in_ty(tcx, *ty, type_ident) {
                return Some(found);
            }
        }
        TyKind::Tuple(tys) => {
            for tuple_ty in tys.iter() {
                if let Some(found) = find_generic_in_ty(tcx, tuple_ty, type_ident) {
                    return Some(found);
                }
            }
        }
        TyKind::Adt(adt_def, substs) => {
            let name = tcx.item_name(adt_def.did()).to_string();
            if name == type_ident {
                return Some(ty);
            }
            for field in adt_def.all_fields() {
                let field_ty = field.ty(tcx, substs);
                if let Some(found) = find_generic_in_ty(tcx, field_ty, type_ident) {
                    return Some(found);
                }
            }
        }
        _ => {}
    }
    None
}

pub fn reflect_generic<'tcx>(
    generic_mapping: &FxHashMap<String, Ty<'tcx>>,
    func_name: &str,
    ty: Ty<'tcx>,
) -> Ty<'tcx> {
    let mut actual_ty = ty;
    match ty.kind() {
        TyKind::Param(param_ty) => {
            let generic_name = param_ty.name.to_string();
            if let Some(actual_ty_from_map) = generic_mapping.get(&generic_name) {
                actual_ty = *actual_ty_from_map;
            }
        }
        _ => {}
    }
    rap_debug!(
        "peel generic ty for {:?}, actual_ty is {:?}",
        func_name,
        actual_ty
    );
    actual_ty
}

// src_var = 0: for constructor
// src_var = 1: for methods
pub fn has_tainted_fields(tcx: TyCtxt, def_id: DefId, src_var: u32) -> bool {
    let mut dataflow_analyzer = DataFlowAnalyzer::new(tcx, false);
    dataflow_analyzer.build_graph(def_id);

    let body = tcx.optimized_mir(def_id);
    let params = &body.args_iter().collect::<Vec<_>>();
    rap_info!("params {:?}", params);
    let self_local = Local::from(src_var);

    let flowing_params: Vec<Local> = params
        .iter()
        .filter(|&&param_local| {
            dataflow_analyzer.has_flow_between(def_id, self_local, param_local)
                && self_local != param_local
        })
        .copied()
        .collect();

    if !flowing_params.is_empty() {
        rap_info!(
            "Taint flow found from self to other parameters: {:?}",
            flowing_params
        );
        true
    } else {
        false
    }
}

// 修改返回值类型为调用链的向量
pub fn get_all_std_unsafe_chains(tcx: TyCtxt, def_id: DefId) -> Vec<Vec<String>> {
    let mut results = Vec::new();
    let mut visited = HashSet::new(); // 避免循环调用
    let mut current_chain = Vec::new();

    // 开始DFS遍历
    dfs_find_unsafe_chains(tcx, def_id, &mut current_chain, &mut results, &mut visited);
    results
}

// DFS递归查找unsafe调用链
fn dfs_find_unsafe_chains(
    tcx: TyCtxt,
    def_id: DefId,
    current_chain: &mut Vec<String>,
    results: &mut Vec<Vec<String>>,
    visited: &mut HashSet<DefId>,
) {
    // 避免循环调用
    if visited.contains(&def_id) {
        return;
    }
    visited.insert(def_id);

    let current_func_name = get_cleaned_def_path_name(tcx, def_id);
    current_chain.push(current_func_name.clone());

    // 获取当前函数的所有unsafe callee
    let unsafe_callees = find_unsafe_callees_in_function(tcx, def_id);

    if unsafe_callees.is_empty() {
        // 如果没有更多的unsafe callee，保存当前链
        results.push(current_chain.clone());
    } else {
        // 对每个unsafe callee继续DFS
        for (callee_def_id, callee_name) in unsafe_callees {
            dfs_find_unsafe_chains(tcx, callee_def_id, current_chain, results, visited);
        }
    }

    // 回溯
    current_chain.pop();
    visited.remove(&def_id);
}

fn find_unsafe_callees_in_function(tcx: TyCtxt, def_id: DefId) -> Vec<(DefId, String)> {
    let mut callees = Vec::new();

    if let Some(body) = try_get_mir(tcx, def_id) {
        for bb in body.basic_blocks.iter() {
            if let Some(terminator) = &bb.terminator {
                if let Some((callee_def_id, callee_name)) = extract_unsafe_callee(tcx, terminator) {
                    callees.push((callee_def_id, callee_name));
                }
            }
        }
    }

    callees
}

fn extract_unsafe_callee(tcx: TyCtxt<'_>, terminator: &Terminator<'_>) -> Option<(DefId, String)> {
    if let TerminatorKind::Call { func, .. } = &terminator.kind {
        if let Operand::Constant(func_constant) = func {
            if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                if check_safety(tcx, *callee_def_id) == Safety::Unsafe {
                    let func_name = get_cleaned_def_path_name(tcx, *callee_def_id);
                    return Some((*callee_def_id, func_name));
                }
            }
        }
    }
    None
}

fn try_get_mir(tcx: TyCtxt<'_>, def_id: DefId) -> Option<&rustc_middle::mir::Body<'_>> {
    if tcx.is_mir_available(def_id) {
        Some(tcx.optimized_mir(def_id))
    } else {
        None
    }
}

pub fn get_cleaned_def_path_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let def_id_str = format!("{:?}", def_id);
    let mut parts: Vec<&str> = def_id_str.split("::").collect();

    let mut remove_first = false;
    if let Some(first_part) = parts.get_mut(0) {
        if first_part.contains("core") {
            *first_part = "core";
        } else if first_part.contains("std") {
            *first_part = "std";
        } else if first_part.contains("alloc") {
            *first_part = "alloc";
        } else {
            remove_first = true;
        }
    }
    if remove_first && !parts.is_empty() {
        parts.remove(0);
    }

    let new_parts: Vec<String> = parts
        .into_iter()
        .filter_map(|s| {
            if s.contains("{") {
                if remove_first {
                    get_struct_name(tcx, def_id)
                } else {
                    None
                }
            } else {
                Some(s.to_string())
            }
        })
        .collect();

    let mut cleaned_path = new_parts.join("::");
    cleaned_path = cleaned_path.trim_end_matches(')').to_string();
    cleaned_path
    // tcx.def_path_str(def_id)
    //     .replace("::", "_")
    //     .replace("<", "_")
    //     .replace(">", "_")
    //     .replace(",", "_")
    //     .replace(" ", "")
    //     .replace("__", "_")
}

pub fn print_unsafe_chains(chains: &[Vec<String>]) {
    if chains.is_empty() {
        return;
    }

    println!("==============================");
    println!("Found {} unsafe call chain(s):", chains.len());
    for (i, chain) in chains.iter().enumerate() {
        println!("Chain {}:", i + 1);
        for (j, func_name) in chain.iter().enumerate() {
            let indent = "  ".repeat(j);
            println!("{}{}-> {}", indent, if j > 0 { " " } else { "" }, func_name);
        }
        println!();
    }
}

pub fn get_all_std_fns_by_rustc_public(tcx: TyCtxt) -> Vec<DefId> {
    let mut all_std_fn_def = Vec::new();
    let mut results = Vec::new();
    let mut core_fn_def: Vec<_> = rustc_public::find_crates("core")
        .iter()
        .flat_map(|krate| krate.fn_defs())
        .collect();
    let mut std_fn_def: Vec<_> = rustc_public::find_crates("std")
        .iter()
        .flat_map(|krate| krate.fn_defs())
        .collect();
    let mut alloc_fn_def: Vec<_> = rustc_public::find_crates("alloc")
        .iter()
        .flat_map(|krate| krate.fn_defs())
        .collect();
    all_std_fn_def.append(&mut core_fn_def);
    all_std_fn_def.append(&mut std_fn_def);
    all_std_fn_def.append(&mut alloc_fn_def);

    for fn_def in &all_std_fn_def {
        let def_id = crate::def_id::to_internal(fn_def, tcx);
        results.push(def_id);
    }
    results
}

pub fn generate_mir_cfg_dot<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    alias_sets: &Vec<FxHashSet<usize>>,
) -> Result<(), std::io::Error> {
    let mir = tcx.optimized_mir(def_id);

    let mut dot_content = String::new();

    let alias_info_str = format!("Alias Sets: {:?}", alias_sets);

    dot_content.push_str(&format!(
        "digraph mir_cfg_{} {{\n",
        get_cleaned_def_path_name(tcx, def_id)
    ));

    dot_content.push_str(&format!(
        "    label = \"MIR CFG for {}\\n{}\\n\";\n",
        tcx.def_path_str(def_id),
        alias_info_str.replace("\"", "\\\"")
    ));
    dot_content.push_str("    labelloc = \"t\";\n");
    dot_content.push_str("    node [shape=box, fontname=\"Courier\", align=\"left\"];\n\n");

    for (bb_index, bb_data) in mir.basic_blocks.iter_enumerated() {
        let mut lines: Vec<String> = bb_data
            .statements
            .iter()
            .map(|stmt| format!("{:?}", stmt))
            .collect();

        let mut node_style = String::new();

        if let Some(terminator) = &bb_data.terminator {
            let mut is_drop_related = false;

            match &terminator.kind {
                TerminatorKind::Drop { .. } => {
                    is_drop_related = true;
                }
                TerminatorKind::Call { func, .. } => {
                    if let Operand::Constant(c) = func
                        && let ty::FnDef(def_id, _) = *c.ty().kind()
                        && is_drop_fn(def_id)
                    {
                        is_drop_related = true;
                    }
                }
                _ => {}
            }

            if is_drop_related {
                node_style = ", style=\"filled\", fillcolor=\"#ffdddd\", color=\"red\"".to_string();
            }

            lines.push(format!("{:?}", terminator.kind));
        } else {
            lines.push("(no terminator)".to_string());
        }

        let label_content = lines.join("\\l");

        let node_label = format!("BB{}:\\l{}\\l", bb_index.index(), label_content);

        dot_content.push_str(&format!(
            "    BB{} [label=\"{}\"{}];\n",
            bb_index.index(),
            node_label.replace("\"", "\\\""),
            node_style
        ));

        if let Some(terminator) = &bb_data.terminator {
            for target in terminator.successors() {
                let edge_label = match terminator.kind {
                    _ => "".to_string(),
                };

                dot_content.push_str(&format!(
                    "    BB{} -> BB{} [label=\"{}\"];\n",
                    bb_index.index(),
                    target.index(),
                    edge_label
                ));
            }
        }
    }
    dot_content.push_str("}\n");
    let name = get_cleaned_def_path_name(tcx, def_id);
    let dot_graph = DotGraph::new(name, dot_content);
    render_dot_string(&dot_graph);
    rap_debug!("render dot for {:?}", def_id);
    Ok(())
}

// Input the adt def id
// Return set of (mutable method def_id, fields can be modified)
pub fn get_all_mutable_methods(tcx: TyCtxt, src_def_id: DefId) -> HashMap<DefId, HashSet<usize>> {
    let mut std_results = HashMap::new();
    if get_type(tcx, src_def_id) == FnKind::Constructor {
        return std_results;
    }
    let all_std_fn_def = get_all_std_fns_by_rustc_public(tcx);
    let target_adt_def = get_adt_def_id_by_adt_method(tcx, src_def_id);
    let mut is_std = false;
    for &def_id in &all_std_fn_def {
        let adt_def = get_adt_def_id_by_adt_method(tcx, def_id);
        if adt_def.is_some() && adt_def == target_adt_def && src_def_id != def_id {
            if has_mut_self_param(tcx, def_id) {
                std_results.insert(def_id, HashSet::new());
            }
            is_std = true;
        }
    }
    if is_std {
        return std_results;
    }
    let mut results = HashMap::new();
    let public_fields = target_adt_def.map_or_else(HashSet::new, |def| get_public_fields(tcx, def));
    let impl_vec = target_adt_def.map_or_else(Vec::new, |def| get_impls_for_struct(tcx, def));
    for impl_id in impl_vec {
        if !matches!(tcx.def_kind(impl_id), rustc_hir::def::DefKind::Impl { .. }) {
            continue;
        }
        let associated_items = tcx.associated_items(impl_id);
        for item in associated_items.in_definition_order() {
            if let ty::AssocKind::Fn {
                name: _,
                has_self: _,
            } = item.kind
            {
                let item_def_id = item.def_id;
                if has_mut_self_param(tcx, item_def_id) {
                    let modified_fields = public_fields.clone();
                    results.insert(item_def_id, modified_fields);
                }
            }
        }
    }
    results
}

pub fn get_cons(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    let mut cons = Vec::new();
    if tcx.def_kind(def_id) == DefKind::Fn || get_type(tcx, def_id) == FnKind::Constructor {
        return cons;
    }
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            // get struct ty
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                let adt_def_id = adt_def.did();
                let impls = tcx.inherent_impls(adt_def_id);
                for impl_def_id in impls {
                    for item in tcx.associated_item_def_ids(impl_def_id) {
                        if (tcx.def_kind(item) == DefKind::Fn
                            || tcx.def_kind(item) == DefKind::AssocFn)
                            && get_type(tcx, *item) == FnKind::Constructor
                        {
                            cons.push(*item);
                        }
                    }
                }
            }
        }
    }
    cons
}

pub fn append_fn_with_types(tcx: TyCtxt, def_id: DefId) -> FnInfo {
    FnInfo::new(def_id, check_safety(tcx, def_id), get_type(tcx, def_id))
}
pub fn search_constructor(tcx: TyCtxt, def_id: DefId) -> Vec<DefId> {
    let mut constructors = Vec::new();
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            // get struct ty
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                let adt_def_id = adt_def.did();
                let impl_vec = get_impls_for_struct(tcx, adt_def_id);
                for impl_id in impl_vec {
                    let associated_items = tcx.associated_items(impl_id);
                    for item in associated_items.in_definition_order() {
                        if let ty::AssocKind::Fn {
                            name: _,
                            has_self: _,
                        } = item.kind
                        {
                            let item_def_id = item.def_id;
                            if get_type(tcx, item_def_id) == FnKind::Constructor {
                                constructors.push(item_def_id);
                            }
                        }
                    }
                }
            }
        }
    }
    constructors
}

pub fn get_ptr_deref_dummy_def_id(tcx: TyCtxt<'_>) -> Option<DefId> {
    tcx.hir_crate_items(()).free_items().find_map(|item_id| {
        let def_id = item_id.owner_id.to_def_id();
        let name = tcx.opt_item_name(def_id)?;

        (name.as_str() == "__raw_ptr_deref_dummy").then_some(def_id)
    })
}
