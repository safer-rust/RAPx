#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use crate::limit::FUZZABLE_MAX_DEPTH;
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), not(rapx_ge_100)))]
use rustc_hir::LangItem;
#[cfg(all(not(rapx_has_attr_ir), rapx_ge_100))]
use rustc_hir::attrs::lang_items::LangItem;
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::find_attr;
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::AttributeKind;
#[cfg(not(rapx_has_attr_ir))]
use rustc_hir::find_attr;
#[cfg(not(rapx_has_attr_ir))]
use rustc_hir::attrs::AttributeKind;
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::sym;
use rustc_type_ir::TypeVisitable;

fn is_fuzzable_std_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, depth: usize) -> bool {
    match ty.kind() {
        ty::Adt(def, args) => {
            if tcx.is_lang_item(def.did(), LangItem::String) {
                return true;
            }
            if tcx.is_diagnostic_item(sym::Vec, def.did())
                && is_fuzzable_ty(args.type_at(0), tcx, depth + 1)
            {
                return true;
            }
            if tcx.is_diagnostic_item(sym::Arc, def.did())
                && is_fuzzable_ty(args.type_at(0), tcx, depth + 1)
            {
                return true;
            }
            false
        }
        _ => false,
    }
}

fn is_non_fuzzable_std_ty<'tcx>(ty: Ty<'tcx>, _tcx: TyCtxt<'tcx>) -> bool {
    let name = format!("{}", ty);
    name.as_str() == "core::alloc::LayoutError"
}

fn ty_contains_region<'tcx>(ty: Ty<'tcx>) -> bool {
    struct Visitor {
        contains_region: bool,
    }
    impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for Visitor {
        fn visit_region(&mut self, _: ty::Region<'tcx>) -> Self::Result {
            self.contains_region = true;
        }
    }
    let mut visitor = Visitor {
        contains_region: false,
    };
    ty.visit_with(&mut visitor);
    visitor.contains_region
}

/// Checks whether the given ADT, or any of its fields/variants, are marked as `#[non_exhaustive]`
///
/// This function is copied from Clippy
pub fn has_non_exhaustive_attr(tcx: TyCtxt<'_>, adt: ty::AdtDef<'_>) -> bool {
    adt.is_variant_list_non_exhaustive()
        || find_attr!(
            crate::compat::get_all_attrs(tcx, adt.did()),
            AttributeKind::NonExhaustive(..)
        )
        || adt.variants().iter().any(|variant_def| {
            variant_def.is_field_list_non_exhaustive()
                || find_attr!(
                    crate::compat::get_all_attrs(tcx, variant_def.def_id),
                    AttributeKind::NonExhaustive(..)
                )
        })
        || adt.all_fields().any(|field_def| {
            find_attr!(
                crate::compat::get_all_attrs(tcx, field_def.did),
                AttributeKind::NonExhaustive(..)
            )
        })
}

pub fn is_fuzzable_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, depth: usize) -> bool {
    if depth > FUZZABLE_MAX_DEPTH {
        return false;
    }

    if is_fuzzable_std_ty(ty, tcx, depth + 1) {
        return true;
    }

    if is_non_fuzzable_std_ty(ty, tcx) {
        return false;
    }

    match ty.kind() {
        // Basical data type
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Float(_)
        | TyKind::Str => true,

        // Infer
        TyKind::Infer(
            ty::InferTy::IntVar(_)
            | ty::InferTy::FreshIntTy(_)
            | ty::InferTy::FloatVar(_)
            | ty::InferTy::FreshFloatTy(_),
        ) => true,

        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Slice(inner_ty) => {
            is_fuzzable_ty(inner_ty.peel_refs(), tcx, depth + 1)
        }

        TyKind::Array(inner_ty, const_) => {
            if const_.try_to_value().is_none() {
                return false;
            }
            is_fuzzable_ty(inner_ty.peel_refs(), tcx, depth + 1)
        }

        // Tuple
        TyKind::Tuple(tys) => tys
            .iter()
            .all(|inner_ty| is_fuzzable_ty(inner_ty.peel_refs(), tcx, depth + 1)),

        // ADT
        TyKind::Adt(adt_def, args) => {
            if adt_def.is_union() || has_non_exhaustive_attr(tcx, *adt_def) {
                return false;
            }
            // if adt contain region, then we consider it non-fuzzable
            if ty_contains_region(ty) {
                return false;
            }

            // if any field is not public or not fuzzable, then we consider it non-fuzzable
            if !adt_def.all_fields().all(|field| {
                field.vis.is_public()
                    && is_fuzzable_ty(field.ty(tcx, args).skip_norm_wip(), tcx, depth + 1)
            }) {
                return false;
            }

            // empty enum cannot be instantiated
            if adt_def.is_enum() && adt_def.variants().is_empty() {
                return false;
            }

            true
        }
        _ => false,
    }
}
