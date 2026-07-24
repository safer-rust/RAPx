//! Generic-parameter helpers for layout-sensitive verify checks.
//!
//! This is the verify-side version of the old Senryx generic helper.  It maps
//! selected generic trait bounds to a finite set of representative concrete
//! types, so SMT lowering can reason about layout requirements that mention
//! generic parameters.

use super::helpers::ty_has_param_const;
use std::collections::{HashMap, HashSet};

use if_chain::if_chain;
use rustc_hir::{ImplPolarity, ItemId, ItemKind, hir_id::OwnerId};
use rustc_middle::ty::{
    FloatTy, IntTy, ParamEnv, Ty, TyCtxt, TyKind, UintTy,
};

/// Representative concrete types satisfying generic trait bounds.
pub struct GenericTypeCandidates<'tcx> {
    trait_map: HashMap<String, HashSet<Ty<'tcx>>>,
}

impl<'tcx> GenericTypeCandidates<'tcx> {
    /// Build generic type candidates from a function definition.
    pub fn for_def(tcx: TyCtxt<'tcx>, def_id: rustc_hir::def_id::DefId) -> Self {
        Self::new(tcx, tcx.param_env(def_id))
    }

    /// Build generic type candidates from a parameter environment.
    pub fn new(tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        let mut trait_bounds: HashMap<String, HashSet<String>> = HashMap::new();
        let mut satisfied_types: HashMap<String, HashSet<Ty<'tcx>>> = HashMap::new();

        for clause in param_env.caller_bounds() {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_def_id = trait_clause.def_id();
            let generic_name = trait_clause.self_ty().skip_binder().to_string();
            let trait_name = tcx.def_path_str(trait_def_id);
            trait_bounds
                .entry(generic_name.clone())
                .or_default()
                .insert(trait_name.clone());

            let type_set = satisfied_types.entry(generic_name).or_default();
            for impl_def_id in tcx.all_impls(trait_def_id) {
                if !impl_def_id.is_local() {
                    continue;
                }
                let impl_owner_id = tcx
                    .hir_owner_node(OwnerId {
                        def_id: impl_def_id.expect_local(),
                    })
                    .def_id();
                let item = tcx.hir_item(ItemId {
                    owner_id: impl_owner_id,
                });
                #[cfg(rapx_rustc_ge_193)]
                let trait_ref_opt = tcx.impl_opt_trait_ref(impl_def_id);
                #[cfg(not(rapx_rustc_ge_193))]
                let trait_ref_opt = tcx.impl_trait_ref(impl_def_id);

                if_chain! {
                    if let ItemKind::Impl(impl_item) = item.kind;
                    if let Some(trait_impl_header) = impl_item.of_trait;
                    if trait_impl_header.polarity == ImplPolarity::Positive;
                    if let Some(binder) = trait_ref_opt;
                    then {
                        let impl_ty = binder.skip_binder().self_ty();
                        match impl_ty.kind() {
                            TyKind::Adt(adt_def, _) => {
                                let ty = tcx.type_of(adt_def.did()).skip_binder();
                                if !ty_has_param_const(ty) {
                                    type_set.insert(ty);
                                }
                            }
                            TyKind::Param(_) => {}
                            _ => {
                                if !ty_has_param_const(impl_ty) {
                                    type_set.insert(impl_ty);
                                }
                            }
                        }
                    }
                }
            }

            if trait_name == "bytemuck::Pod" || trait_name == "plain::Plain" {
                type_set.extend(Self::pod_types(tcx));
            }
        }

        let std_marker_traits = HashSet::from([
            String::from("std::marker::Copy"),
            String::from("std::clone::Clone"),
            String::from("std::marker::Sized"),
        ]);
        for (name, type_set) in &mut satisfied_types {
            if trait_bounds
                .get(name)
                .map(|bounds| bounds.is_subset(&std_marker_traits))
                .unwrap_or(false)
            {
                type_set.clear();
            }
        }

        Self {
            trait_map: satisfied_types,
        }
    }

    /// Return the representative types for a generic parameter name.
    pub fn candidates_for(&self, generic_name: &str) -> Option<&HashSet<Ty<'tcx>>> {
        self.trait_map.get(generic_name)
    }

    /// Return representative types for a generic parameter type.
    pub fn candidates_for_ty(&self, ty: Ty<'tcx>) -> Option<&HashSet<Ty<'tcx>>> {
        let TyKind::Param(_) = ty.kind() else {
            return None;
        };
        self.candidates_for(&ty.to_string())
    }

    fn pod_types(tcx: TyCtxt<'tcx>) -> HashSet<Ty<'tcx>> {
        [
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::Isize)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I8)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I16)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I32)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I64)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I128)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::Usize)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U8)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U16)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U32)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U64)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U128)),
            tcx.mk_ty_from_kind(TyKind::Float(FloatTy::F32)),
            tcx.mk_ty_from_kind(TyKind::Float(FloatTy::F64)),
        ]
        .into_iter()
        .collect()
    }
}
