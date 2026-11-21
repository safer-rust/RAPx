//! Verify and report obligations of unsafe `Send`/`Sync` implementations.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use crate::compat::FxHashMap;
use crate::contract::{Property, PropertyArg, PropertyKind, place::field_name_from_arg};

use super::{
    auto_trait::{
        atomic_update_check, contain_no_type_check, field_invariant_check, no_internal_mut_check,
        no_raw_ptr_check, ref_send_check, uni_internal_mut_check,
    },
    report::{CheckResult, UnknownReason},
    trait_ensurance::{MarkerTraitKind, TraitEnsurance, TraitEnsuranceKind},
};

pub(super) struct MarkerTraitVerifier<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    struct_invariant_results: &'a FxHashMap<DefId, CheckResult>,
}

impl<'a, 'tcx> MarkerTraitVerifier<'a, 'tcx> {
    pub(super) fn new(
        tcx: TyCtxt<'tcx>,
        struct_invariant_results: &'a FxHashMap<DefId, CheckResult>,
    ) -> Self {
        Self {
            tcx,
            struct_invariant_results,
        }
    }

    /// Structurally verify collected `Send`/`Sync` marker-trait impls.
    pub(super) fn emit(&self, units: &[&TraitEnsurance<'tcx>]) {
        for unit in units {
            let TraitEnsuranceKind::Marker(kind, obligations) = &unit.kind else {
                continue;
            };
            let trait_name = match kind {
                MarkerTraitKind::Send => "Send",
                MarkerTraitKind::Sync => "Sync",
            };
            let is_sync = matches!(kind, MarkerTraitKind::Sync);
            let self_ty_label = unit
                .self_ty_def_id
                .map(|d| self.tcx.def_path_str(d))
                .unwrap_or_else(|| "<unknown>".to_string());

            rap_info!("============================================================");
            rap_info!("[rapx::verify] unsafe impl {trait_name} for {self_ty_label}");
            rap_info!("============================================================");

            if obligations.is_empty() {
                rap_info!("  ensures: <none>");
            }

            let mut any_failed = false;
            let mut any_unknown = false;
            for property in obligations {
                let Some(self_ty) = unit
                    .self_ty_def_id
                    .map(|d| self.tcx.type_of(d).skip_binder())
                else {
                    any_unknown = true;
                    continue;
                };
                let result =
                    self.check_type_obligation(property, unit.impl_def_id, self_ty, is_sync);
                let label = property.display_for_report(self.tcx, unit.self_ty_def_id, None);
                let verdict = match result {
                    CheckResult::ProvedByRule | CheckResult::ProvedBySmt => "PROVED",
                    CheckResult::Failed => "FAILED",
                    CheckResult::Unknown(_) => "UNKNOWN",
                };
                rap_info!("  - {label} => {verdict}");
                any_failed |= matches!(result, CheckResult::Failed);
                any_unknown |= matches!(result, CheckResult::Unknown(_));
            }

            let verdict = if any_failed {
                "UNSAFE (obligation failed)"
            } else if any_unknown {
                "UNKNOWN"
            } else {
                "SAFE (all obligations proved)"
            };
            rap_info!("  verdict: {verdict}");
            rap_info!("");
        }
    }

    /// Dispatch a single type-level obligation (`ContainNoType` / `NoRawPtr` /
    /// `NoInternalMut` / `UniInternalMut` / `AtomicUpdate` / `Allocated` /
    /// `Owning` / `RefSend`).
    fn check_type_obligation(
        &self,
        property: &Property<'tcx>,
        impl_def_id: DefId,
        self_ty: Ty<'tcx>,
        is_sync: bool,
    ) -> CheckResult {
        match property {
            Property::Atom(atom) => match atom.kind {
                PropertyKind::ContainNoType => {
                    let Some(ty) = atom.args.first().and_then(|a| match a {
                        PropertyArg::Ty(t) => Some(*t),
                        _ => None,
                    }) else {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    };
                    let negatives: Vec<String> = atom.args[1..]
                        .iter()
                        .filter_map(|a| match a {
                            PropertyArg::Ident(n) => Some(n.clone()),
                            _ => None,
                        })
                        .collect();
                    contain_no_type_check(self.tcx, ty, &negatives, impl_def_id, is_sync)
                }
                PropertyKind::NoRawPtr => {
                    let Some(ty) = atom.args.first().and_then(|a| match a {
                        PropertyArg::Ty(t) => Some(*t),
                        _ => None,
                    }) else {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    };
                    no_raw_ptr_check(self.tcx, ty, impl_def_id, is_sync)
                }
                PropertyKind::NoInternalMut => {
                    let Some(ty) = atom.args.first().and_then(|a| match a {
                        PropertyArg::Ty(t) => Some(*t),
                        _ => None,
                    }) else {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    };
                    no_internal_mut_check(self.tcx, ty)
                }
                PropertyKind::UniInternalMut => {
                    let Some(ty) = atom.args.first().and_then(|a| match a {
                        PropertyArg::Ty(t) => Some(*t),
                        _ => None,
                    }) else {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    };
                    uni_internal_mut_check(self.tcx, ty)
                }
                PropertyKind::Allocated | PropertyKind::Owning => {
                    // Type-level `Allocated(ptr, T, n)` / `Owning(ptr)` reached
                    // through a `TamedRawPtr` compound: check that the type declares
                    // a matching `#[rapx::invariant(...)]` (optionally restricted to
                    // the field named in the property) and that it verified.
                    let adt_def_id = match self_ty.kind() {
                        TyKind::Adt(adt_def, _) => adt_def.did(),
                        _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
                    };
                    let field = atom
                        .args
                        .first()
                        .and_then(|a| field_name_from_arg(self.tcx, adt_def_id, a));
                    field_invariant_check(
                        self.tcx,
                        self_ty,
                        atom.kind,
                        field.as_deref(),
                        &self.struct_invariant_results,
                    )
                }
                PropertyKind::AtomicUpdate => {
                    let Some(ty) = atom.args.first().and_then(|a| match a {
                        PropertyArg::Ty(t) => Some(*t),
                        _ => None,
                    }) else {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    };
                    atomic_update_check(self.tcx, ty, impl_def_id, is_sync)
                }
                PropertyKind::RefSend => {
                    let Some(ty) = atom.args.first().and_then(|a| match a {
                        PropertyArg::Ty(t) => Some(*t),
                        _ => None,
                    }) else {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    };
                    ref_send_check(self.tcx, ty, impl_def_id, is_sync)
                }
                _ => CheckResult::Unknown(UnknownReason::Unimplemented),
            },
            Property::And(and) => {
                let mut overall = CheckResult::ProvedByRule;
                for conjunct in &and.conjuncts {
                    overall = overall.and(self.check_type_obligation(
                        conjunct,
                        impl_def_id,
                        self_ty,
                        is_sync,
                    ));
                }
                overall
            }
            Property::Or(or) => {
                CheckResult::disjunction_with_guards(or.disjuncts.iter().map(|disjunct| {
                    (
                        self.check_type_obligation(disjunct, impl_def_id, self_ty, is_sync),
                        true,
                    )
                }))
            }
        }
    }
}
