use rustc_hir::LangItem;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::sym;

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
    match name.as_str() {
        "core::alloc::LayoutError" => return true,
        _ => {}
    }
    false
}

const MAX_DEPTH: usize = 64;
pub fn is_fuzzable_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>, depth: usize) -> bool {
    if depth > MAX_DEPTH {
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
            if adt_def.is_union() {
                return false;
            }

            if adt_def.is_variant_list_non_exhaustive() {
                return false;
            }

            // if adt contain region, then we consider it non-fuzzable
            if args.iter().any(|arg| arg.as_region().is_some()) {
                return false;
            }

            // if any field is not public or not fuzzable, then we consider it non-fuzzable
            if !adt_def.all_fields().all(|field| {
                field.vis.is_public() && is_fuzzable_ty(field.ty(tcx, args), tcx, depth + 1)
            }) {
                return false;
            }

            // empty enum cannot be instantiated
            if adt_def.is_enum() && adt_def.variants().is_empty() {
                return false;
            }

            true
        }

        // 其他类型默认不可 Fuzz
        _ => false,
    }
}
