use rustc_abi::FieldIdx;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{BasicBlock, Operand, TerminatorKind, UnwindAction},
    ty::{self, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use serde_json::Value;
use syn::Expr;

/// Stable MIR location for a call terminator inside one function body.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct CallsiteLocation {
    /// Function containing the call terminator.
    pub caller: DefId,
    /// Basic block whose terminator is the call.
    pub block: BasicBlock,
}

/// A concrete unsafe callsite in one MIR body.
#[derive(Clone, Debug)]
pub struct Callsite<'tcx> {
    /// Function containing this call.
    pub caller: DefId,
    /// Unsafe callee being invoked.
    pub callee: DefId,
    /// MIR block whose terminator is the call.
    pub block: BasicBlock,
    /// Source span attached to the MIR call terminator.
    pub span: Span,
    /// MIR operands passed to the callee.
    pub args: Vec<Operand<'tcx>>,
}

impl<'tcx> Callsite<'tcx> {
    /// Return the MIR location that identifies this callsite inside the verifier.
    pub fn location(&self) -> CallsiteLocation {
        CallsiteLocation {
            caller: self.caller,
            block: self.block,
        }
    }

    /// Return a stable human-readable callee path for diagnostics.
    pub fn callee_name(&self, tcx: TyCtxt<'tcx>) -> String {
        get_cleaned_def_path_name(tcx, self.callee)
    }
}

/// Collect all unsafe MIR callsites in `def_id`.
pub fn collect_unsafe_callsites<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Callsite<'tcx>> {
    let mut callsites = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return callsites;
    }

    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func,
            args,
            fn_span,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };

        let Operand::Constant(func_constant) = func else {
            continue;
        };

        let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() else {
            continue;
        };

        if check_safety(tcx, *callee_def_id) != Safety::Unsafe {
            continue;
        }

        callsites.push(Callsite {
            caller: def_id,
            callee: *callee_def_id,
            block: bb,
            span: *fn_span,
            args: args.iter().map(|arg| arg.node.clone()).collect(),
        });
    }

    callsites
}

/// A compact MIR CFG used by the verifier path extractor.
#[derive(Clone, Debug)]
pub struct CFG {
    pub entry: BasicBlock,
    pub successors: Vec<Vec<BasicBlock>>,
}

impl CFG {
    /// Build a successor graph from optimized MIR.
    pub fn new(tcx: TyCtxt<'_>, def_id: DefId) -> Self {
        let body = tcx.optimized_mir(def_id);
        let successors = body
            .basic_blocks
            .iter()
            .map(|block| terminator_successors(&block.terminator().kind))
            .collect();
        Self {
            entry: BasicBlock::from_usize(0),
            successors,
        }
    }

    /// Return successors of a block.
    pub fn successors(&self, block: BasicBlock) -> &[BasicBlock] {
        self.successors
            .get(block.as_usize())
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

/// Compute MIR successor blocks for one terminator.
///
/// The extractor includes normal successors and cleanup successors so the
/// skeleton reflects all CFG edges that can affect reachability.  Later phases
/// may decide whether a cleanup path is relevant to a particular obligation.
fn terminator_successors(kind: &TerminatorKind<'_>) -> Vec<BasicBlock> {
    let mut successors = Vec::new();
    match kind {
        TerminatorKind::Goto { target } => successors.push(*target),
        TerminatorKind::SwitchInt { targets, .. } => {
            successors.extend(targets.all_targets().iter().copied());
        }
        TerminatorKind::Drop { target, unwind, .. }
        | TerminatorKind::Assert { target, unwind, .. } => {
            successors.push(*target);
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::Call { target, unwind, .. } => {
            if let Some(target) = target {
                successors.push(*target);
            }
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::Yield { resume, drop, .. } => {
            successors.push(*resume);
            if let Some(drop) = drop {
                successors.push(*drop);
            }
        }
        TerminatorKind::FalseEdge { real_target, .. } => successors.push(*real_target),
        TerminatorKind::FalseUnwind {
            real_target,
            unwind,
        } => {
            successors.push(*real_target);
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::InlineAsm {
            targets, unwind, ..
        } => {
            successors.extend(targets.iter().copied());
            push_unwind_target(unwind, &mut successors);
        }
        TerminatorKind::Return
        | TerminatorKind::Unreachable
        | TerminatorKind::UnwindResume
        | TerminatorKind::UnwindTerminate(_)
        | TerminatorKind::CoroutineDrop
        | TerminatorKind::TailCall { .. } => {}
    }
    successors.sort_unstable_by_key(|bb| bb.as_usize());
    successors.dedup();
    successors
}

/// Append a cleanup unwind target when one exists.
fn push_unwind_target(unwind: &UnwindAction, successors: &mut Vec<BasicBlock>) {
    if let UnwindAction::Cleanup(target) = unwind {
        successors.push(*target);
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
}

pub fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(expr) {
        let (param_names, param_tys) = parse_signature(tcx, def_id);
        if param_names[0] != "0" {
            if let Some(param_index) = param_names.iter().position(|name| name == &base_ident) {
                return resolve_projection_from_base_ident(
                    tcx,
                    base_ident,
                    fields,
                    param_index + 1,
                    param_tys[param_index],
                );
            }
        }

        if let Some(struct_ty) = get_struct_self_ty(tcx, def_id) {
            return resolve_projection_from_struct_ident(tcx, base_ident, fields, struct_ty);
        }
    }
    None
}

pub fn parse_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    if def_id.as_local().is_some() {
        parse_local_signature(tcx, def_id)
    } else {
        parse_outside_signature(tcx, def_id)
    }
}

pub fn parse_local_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let local_def_id = def_id.as_local().unwrap();
    let hir_body = tcx.hir_body_owned_by(local_def_id);
    if hir_body.params.is_empty() {
        return (vec!["0".to_string()], Vec::new());
    }

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

fn parse_outside_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let sig = tcx.fn_sig(def_id).skip_binder();
    let param_tys: Vec<Ty<'tcx>> = sig.inputs().skip_binder().iter().copied().collect();

    if let Some(args_name) = get_known_std_names(tcx, def_id) {
        return (args_name, param_tys);
    }

    let args_name = (0..param_tys.len()).map(|i| format!("{}", i)).collect();
    (args_name, param_tys)
}

fn get_known_std_names<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<String>> {
    let std_func_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data = get_std_api_signature_json();

    if let Some(arg_info) = json_data.get(&std_func_name) {
        if let Some(args_name) = arg_info.as_array() {
            if args_name.is_empty() {
                return Some(vec!["0".to_string()]);
            }
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

fn get_std_api_signature_json() -> Value {
    serde_json::from_str(include_str!("../analysis/utils/data/std_sig.json"))
        .expect("Unable to parse JSON")
}

pub fn access_ident_recursive(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Path(syn::ExprPath { path, .. }) => {
            if path.segments.len() == 1 {
                let ident = path.segments[0].ident.to_string();
                Some((ident, Vec::new()))
            } else {
                None
            }
        }
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

pub fn parse_expr_into_number(expr: &Expr) -> Option<usize> {
    if let Expr::Lit(expr_lit) = expr {
        if let syn::Lit::Int(lit_int) = &expr_lit.lit {
            return lit_int.base10_parse::<usize>().ok();
        }
    }
    None
}

pub fn match_ty_with_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: String,
) -> Option<Ty<'tcx>> {
    if let Some(primitive_ty) = match_primitive_type(tcx, type_ident.clone()) {
        return Some(primitive_ty);
    }
    find_generic_param(tcx, def_id, type_ident)
}

fn match_primitive_type<'tcx>(tcx: TyCtxt<'tcx>, type_ident: String) -> Option<Ty<'tcx>> {
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

fn find_generic_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: String,
) -> Option<Ty<'tcx>> {
    let (_, param_tys) = parse_signature(tcx, def_id);
    for &ty in &param_tys {
        if let Some(found) = find_generic_in_ty(tcx, ty, &type_ident) {
            return Some(found);
        }
    }

    if let Some(struct_ty) = get_struct_self_ty(tcx, def_id) {
        if let Some(found) = find_generic_in_ty(tcx, struct_ty, &type_ident) {
            return Some(found);
        }
    }

    None
}

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

fn get_struct_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
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

fn get_struct_self_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Ty<'tcx>> {
    let assoc_item = tcx.opt_associated_item(def_id)?;
    let impl_id = assoc_item.impl_container(tcx)?;
    let self_ty = tcx.type_of(impl_id).skip_binder();
    match self_ty.kind() {
        TyKind::Adt(_, _) => Some(self_ty),
        _ => None,
    }
}

fn resolve_projection_from_base_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ident: String,
    fields: Vec<String>,
    base_local: usize,
    base_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let mut current_ty = base_ty;
    let mut field_indices = Vec::new();
    for field_name in fields {
        let Some((field_idx, field_ty)) = resolve_next_field(tcx, current_ty, &field_name) else {
            return if field_indices.is_empty() && base_ident.is_empty() {
                None
            } else {
                None
            };
        };
        current_ty = field_ty;
        field_indices.push((field_idx, current_ty));
    }
    Some((base_local, field_indices, current_ty))
}

fn resolve_projection_from_struct_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ident: String,
    fields: Vec<String>,
    struct_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let Some((field_idx, field_ty)) = resolve_next_field(tcx, struct_ty, &base_ident) else {
        return None;
    };

    let mut current_ty = field_ty;
    let mut field_indices = vec![(field_idx, current_ty)];
    for field_name in fields {
        let Some((next_field_idx, next_field_ty)) =
            resolve_next_field(tcx, current_ty, &field_name)
        else {
            return None;
        };
        current_ty = next_field_ty;
        field_indices.push((next_field_idx, current_ty));
    }

    Some((1, field_indices, current_ty))
}

fn resolve_next_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ty: Ty<'tcx>,
    field_name: &str,
) -> Option<(usize, Ty<'tcx>)> {
    let peeled_ty = base_ty.peel_refs();
    if let TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
        let variant = adt_def.non_enum_variant();
        if let Ok(field_idx) = field_name.parse::<usize>() {
            if field_idx < variant.fields.len() {
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)].ty(tcx, arg_list);
                return Some((field_idx, field_ty));
            }
        }
        if let Some((idx, _)) = variant
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.ident(tcx).name.to_string() == field_name)
        {
            let field_ty = variant.fields[FieldIdx::from_usize(idx)].ty(tcx, arg_list);
            return Some((idx, field_ty));
        }
    }
    None
}

pub(crate) fn check_safety(tcx: TyCtxt<'_>, def_id: DefId) -> Safety {
    let poly_fn_sig = tcx.fn_sig(def_id);
    let fn_sig = poly_fn_sig.skip_binder();
    fn_sig.safety()
}
