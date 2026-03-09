use std::collections::{HashMap, HashSet};

use if_chain::if_chain;
use rustc_hir::{ImplPolarity, ItemId, ItemKind, hir_id::OwnerId};
use rustc_middle::ty::{FloatTy, IntTy, ParamEnv, Ty, TyCtxt, TyKind, UintTy};
// use crate::rap_info;

pub struct GenericChecker<'tcx> {
    // tcx: TyCtxt<'tcx>,
    trait_map: HashMap<String, HashSet<Ty<'tcx>>>,
}

impl<'tcx> GenericChecker<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, p_env: ParamEnv<'tcx>) -> Self {
        let mut trait_bnd_map_for_generic: HashMap<String, HashSet<String>> = HashMap::new();
        let mut satisfied_ty_map_for_generic: HashMap<String, HashSet<Ty<'tcx>>> = HashMap::new();

        for cb in p_env.caller_bounds() {
            // cb: Binder(TraitPredicate(<Self as trait>, ..)
            // Focus on the trait bound applied to our generic parameter

            if let Some(trait_pred) = cb.as_trait_clause() {
                let trait_def_id = trait_pred.def_id();
                let generic_name = trait_pred.self_ty().skip_binder().to_string();
                let satisfied_ty_set = satisfied_ty_map_for_generic
                    .entry(generic_name.clone())
                    .or_insert_with(|| HashSet::new());
                let trait_name = tcx.def_path_str(trait_def_id);
                let trait_bnd_set = trait_bnd_map_for_generic
                    .entry(generic_name)
                    .or_insert_with(|| HashSet::new());
                trait_bnd_set.insert(trait_name.clone());

                // for each implementation
                for def_id in tcx.all_impls(trait_def_id) {
                    // impl_id: LocalDefId
                    if !def_id.is_local() {
                        continue;
                    }
                    let impl_owner_id = tcx
                        .hir_owner_node(OwnerId {
                            def_id: def_id.expect_local(),
                        })
                        .def_id();

                    let item = tcx.hir_item(ItemId {
                        owner_id: impl_owner_id,
                    });
                    if_chain! {
                        if let ItemKind::Impl(impl_item) = item.kind;
                        if let Some(trait_impl_header) = impl_item.of_trait;
                        if trait_impl_header.polarity == ImplPolarity::Positive;
                        if let Some(binder) = tcx.impl_trait_ref(def_id);
                        then {
                            let trait_ref = binder.skip_binder();
                            let impl_ty = trait_ref.self_ty();
                            match impl_ty.kind() {
                                TyKind::Adt(adt_def, _impl_trait_substs) => {
                                    let adt_did = adt_def.did();
                                    let adt_ty = tcx.type_of(adt_did).skip_binder();
                                    // rap_info!("{} is implemented on adt({:?})", trait_name, adt_ty);
                                    satisfied_ty_set.insert(adt_ty);
                                },
                                TyKind::Param(p_ty) => {
                                    let _param_ty = p_ty.to_ty(tcx);
                                },
                                _ => {
                                    // rap_info!("{} is implemented on {:?}", trait_name, impl_ty);
                                    satisfied_ty_set.insert(impl_ty);
                                },
                            }
                        }
                    }
                }

                // handle known external trait e.g., Pod
                if trait_name == "bytemuck::Pod" || trait_name == "plain::Plain" {
                    let ty_bnd = Self::get_satisfied_ty_for_pod(tcx);
                    satisfied_ty_set.extend(&ty_bnd);
                    // rap_info!("current trait bound type set: {:?}", satisfied_ty_set);
                }
            }
        }

        // check trait_bnd_set
        let std_trait_set = HashSet::from([
            String::from("std::marker::Copy"),
            String::from("std::clone::Clone"),
            String::from("std::marker::Sized"),
        ]);
        // if all trait_bound is std::marker, then we could assume it to be arbitrary type
        // to avoid messing up with build type manually
        // we just clear the satisfied ty set
        for (key, satisfied_ty_set) in &mut satisfied_ty_map_for_generic {
            let trait_bnd_set = trait_bnd_map_for_generic
                .entry(key.clone())
                .or_insert_with(|| HashSet::new());
            if trait_bnd_set.is_subset(&std_trait_set) {
                satisfied_ty_set.clear();
            }
        }

        // rap_info!("trait bound type map: {:?}", satisfied_ty_map_for_generic);

        GenericChecker {
            trait_map: satisfied_ty_map_for_generic,
        }
    }

    pub fn get_satisfied_ty_map(&self) -> HashMap<String, HashSet<Ty<'tcx>>> {
        self.trait_map.clone()
    }

    fn get_satisfied_ty_for_pod(tcx: TyCtxt<'tcx>) -> HashSet<Ty<'tcx>> {
        let mut satisfied_ty_set_for_pod: HashSet<Ty<'tcx>> = HashSet::new();
        // f64, u64, i8, i32, u8, i16, u16, u32, usize, i128, isize, i64, u128, f32
        let pod_ty = [
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
        ];

        for pt in pod_ty.iter() {
            satisfied_ty_set_for_pod.insert(*pt);
        }
        satisfied_ty_set_for_pod.clone()
    }
}
