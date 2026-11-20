//! Expanded contract display for `--debug-contracts`.

use rustc_hir::def_id::DefId;

use crate::compat::FxHashMap;
use crate::helpers::name::short_fn_name;

use super::{
    VerifyDriver,
    contract::PropertyKind,
    display::{dedup_compound_props, fmt_contract_expanded, fmt_fn_path_with_generics, fmt_fn_with_params},
    target::FunctionTarget,
    trait_ensurance::{MarkerTraitKind, TraitEnsurance, TraitEnsuranceKind},
};

impl<'tcx> VerifyDriver<'tcx> {
    pub(super) fn print_contracts_debug(
        &self,
        targets: &[FunctionTarget<'tcx>],
        trait_targets: &[TraitEnsurance<'tcx>],
    ) {
        rap_info!("{:=<1$}", "", 76);
        rap_info!("[rapx::debug-contracts] Expanded Contract Assertions");
        rap_info!("{:=<1$}", "", 76);
        rap_info!("");

        let mut struct_groups: FxHashMap<DefId, Vec<&FunctionTarget<'tcx>>> = FxHashMap::default();
        let mut free_targets: Vec<&FunctionTarget<'tcx>> = Vec::new();

        for target in targets {
            if let Some(sid) = target.owner_struct_def_id {
                struct_groups.entry(sid).or_default().push(target);
            } else {
                free_targets.push(target);
            }
        }

        let mut struct_ids: Vec<_> = struct_groups.keys().copied().collect();
        struct_ids.sort_by_key(|did| self.tcx.def_path_str(*did));

        for struct_def_id in struct_ids {
            let methods = &struct_groups[&struct_def_id];
            let struct_name = self.tcx.def_path_str(struct_def_id);

            let inv_target = methods.iter().find(|t| !t.struct_invariants.is_empty());
            let have_invariants = inv_target.is_some();

            if have_invariants || methods.iter().any(|t| self.has_printable_contracts(t)) {
                rap_info!("{:=<1$}", "", 76);
                rap_info!("[rapx::debug-contracts] struct: {struct_name}");
                rap_info!("{:=<1$}", "", 76);
            }

            if let Some(tgt) = inv_target {
                rap_info!("  [Struct Invariants]:");
                let invariants = dedup_compound_props(tgt.struct_invariants.iter());
                let inv_count = invariants.len();
                for (ii, property) in invariants.iter().enumerate() {
                    let ibranch = if ii + 1 == inv_count { "`-" } else { "|-" };
                    let (call, meaning) = fmt_contract_expanded(
                        self.tcx,
                        property,
                        tgt.owner_struct_def_id,
                        Some(tgt.def_id),
                    );
                    self.print_contract_lines("  ", ibranch, &call, &meaning);
                }
                rap_info!("");
            }

            let mut printed = false;
            for (mi, target) in methods.iter().enumerate() {
                let is_last_method = mi + 1 == methods.len();
                let branch = if is_last_method { "`-" } else { "|-" };
                let cont = if is_last_method { "  " } else { "| " };
                if self.print_target_contracts(target, branch, cont) {
                    printed = true;
                }
            }
            if printed {
                rap_info!("{:=<1$}", "", 76);
                rap_info!("");
            }
        }

        for target in &free_targets {
            self.print_target_contracts(target, "- ", "  ");
        }

        let mut traits = trait_targets.iter().collect::<Vec<_>>();
        traits.sort_by_key(|t| self.tcx.def_path_str(t.def_id));
        for trait_target in traits {
            match &trait_target.kind {
                TraitEnsuranceKind::Unsafe(ensures) => {
                    let trait_path = self.tcx.def_path_str(trait_target.def_id);
                    rap_info!("{:=<1$}", "", 76);
                    rap_info!("[rapx::debug-contracts] unsafe trait: {trait_path}");
                    rap_info!("{:=<1$}", "", 76);
                    if let Some(self_ty) = trait_target.self_ty_def_id {
                        rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
                    }
                    if ensures.is_empty() {
                        rap_info!("  ensures: <none>");
                    } else {
                        for (method_name, contracts) in ensures {
                            rap_info!("  fn {method_name}:");
                            for property in dedup_compound_props(contracts.iter()) {
                                let (call, meaning) = fmt_contract_expanded(
                                    self.tcx,
                                    property,
                                    trait_target.self_ty_def_id,
                                    Some(trait_target.def_id),
                                );
                                self.print_contract_lines("  ", "|-", &call, &meaning);
                            }
                        }
                    }
                    rap_info!("");
                }
                TraitEnsuranceKind::Marker(kind, obligations) => {
                    let name = match kind {
                        MarkerTraitKind::Send => "Send",
                        MarkerTraitKind::Sync => "Sync",
                    };
                    rap_info!("{:=<1$}", "", 76);
                    rap_info!("[rapx::debug-contracts] marker trait: {name}");
                    rap_info!("{:=<1$}", "", 76);
                    if let Some(self_ty) = trait_target.self_ty_def_id {
                        rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
                    }
                    if obligations.is_empty() {
                        rap_info!("  obligations: <none>");
                    } else {
                        for property in obligations {
                            let (call, meaning) = fmt_contract_expanded(
                                self.tcx,
                                property,
                                trait_target.self_ty_def_id,
                                None,
                            );
                            self.print_contract_lines("  ", "|-", &call, &meaning);
                        }
                    }
                    rap_info!("");
                }
            }
        }
    }

    fn is_unsafe_fn(&self, def_id: DefId) -> bool {
        self.tcx.fn_sig(def_id).skip_binder().safety() == rustc_hir::Safety::Unsafe
    }

    fn has_caller_contracts(&self, target: &FunctionTarget<'tcx>, is_unsafe_fn: bool) -> bool {
        is_unsafe_fn
            && target
                .caller_requires
                .iter()
                .any(|p| p.kind() != Some(PropertyKind::Unknown))
    }

    fn has_printable_contracts(&self, target: &FunctionTarget<'tcx>) -> bool {
        let is_unsafe_fn = self.is_unsafe_fn(target.def_id);
        self.has_caller_contracts(target, is_unsafe_fn)
            || target
                .callee_requires
                .values()
                .any(|c| c.iter().any(|p| p.kind() != Some(PropertyKind::Unknown)))
    }

    fn print_contract_lines(&self, prefix: &str, branch: &str, call: &str, meaning: &str) {
        rap_info!("{prefix}{branch} {call}");
        let cont = if branch == "`-" { "  " } else { "| " };
        for line in meaning.lines() {
            rap_info!("{prefix}{cont} {line}");
        }
    }

    fn print_target_contracts(
        &self,
        target: &FunctionTarget<'tcx>,
        branch: &str,
        cont: &str,
    ) -> bool {
        let (arg_names_typed, ret_ty) = self.resolve_arg_names_with_types(target.def_id);
        let is_unsafe_fn = self.is_unsafe_fn(target.def_id);

        let target_path = fmt_fn_path_with_generics(self.tcx, target.def_id);
        let short_name = short_fn_name(self.tcx, target.def_id);

        let has_caller = self.has_caller_contracts(target, is_unsafe_fn);
        let mut callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        callee_ids.retain(|did| {
            target
                .callee_requires
                .get(did)
                .is_some_and(|c| c.iter().any(|p| p.kind() != Some(PropertyKind::Unknown)))
        });
        callee_ids.sort_by_key(|did| self.tcx.def_path_str(*did));
        let has_callees = !callee_ids.is_empty();

        if !has_caller && !has_callees {
            return false;
        }

        let fn_display = fmt_fn_with_params(&target_path, &arg_names_typed, ret_ty.as_deref());
        let header = format!("--- method: {short_name}");
        let dashes = 72usize.saturating_sub(header.len());
        rap_info!("{branch} {header} {}", "-".repeat(dashes));
        rap_info!("{cont}  {fn_display}");

        // Caller Contracts (only for unsafe functions)
        if has_caller {
            rap_info!("{cont}  [Caller Contracts]:");
            let caller_props = dedup_compound_props(
                target.caller_requires.iter().filter(|p| p.kind() != Some(PropertyKind::Unknown)),
            );
            for (pi, property) in caller_props.iter().enumerate() {
                let is_last = pi + 1 == caller_props.len();
                let pbranch = if is_last { "`-" } else { "|-" };
                let (call, meaning) = fmt_contract_expanded(
                    self.tcx,
                    property,
                    target.owner_struct_def_id,
                    Some(target.def_id),
                );
                self.print_contract_lines(&format!("{cont}  "), pbranch, &call, &meaning);
            }
            if !has_callees {
                rap_info!("");
            }
        }

        // Callee Contracts (for each unsafe callee)
        if has_callees {
            rap_info!("{cont}  [Unsafe Callees]:");
            for (ci, &callee_id) in callee_ids.iter().enumerate() {
                let is_last_callee = ci + 1 == callee_ids.len();
                let cbranch = if is_last_callee { "`-" } else { "|-" };
                let ccont = if is_last_callee { "  " } else { "| " };
                let contracts = target.callee_requires.get(&callee_id).unwrap();
                let (callee_typed, callee_ret) = self.resolve_arg_names_with_types(callee_id);
                let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                rap_info!(
                    "{cont}  {cbranch} {}",
                    fmt_fn_with_params(&callee_path, &callee_typed, callee_ret.as_deref())
                );
                let props = dedup_compound_props(
                    contracts.iter().filter(|p| p.kind() != Some(PropertyKind::Unknown)),
                );
                for (pi, property) in props.iter().enumerate() {
                    let is_last_prop = pi + 1 == props.len();
                    let pbranch = if is_last_prop { "`-" } else { "|-" };
                    let (call, meaning) = fmt_contract_expanded(self.tcx, property, None, Some(callee_id));
                    self.print_contract_lines(
                        &format!("{cont}  {ccont}"),
                        pbranch,
                        &call,
                        &meaning,
                    );
                }
            }
        }

        rap_info!("");
        true
    }

    fn resolve_arg_names_with_types(&self, def_id: DefId) -> (Vec<String>, Option<String>) {
        if !self.tcx.is_mir_available(def_id) {
            return (Vec::new(), None);
        }
        let body = self.tcx.optimized_mir(def_id);
        let args: Vec<String> = body
            .local_decls
            .iter()
            .enumerate()
            .skip(1)
            .take(body.arg_count)
            .map(|(i, decl)| {
                let name = {
                    let span = decl.source_info.span;
                    self.tcx
                        .sess
                        .source_map()
                        .span_to_snippet(span)
                        .unwrap_or_else(|_| format!("_{}", i))
                };
                let ty = decl.ty.to_string();
                format!("{name}: {ty}")
            })
            .collect();
        let ret_ty = self.tcx.fn_sig(def_id).skip_binder().output().skip_binder();
        let ret_ty = if ret_ty.is_unit() {
            None
        } else {
            Some(ret_ty.to_string())
        };
        (args, ret_ty)
    }
}
