use std::hash::Hash;
use std::ops::Deref;

use super::transform::TransformKind;
use rustc_infer::infer::TyCtxtInferExt;
use rustc_infer::traits::{Obligation, ObligationCause};
use rustc_middle::traits;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_trait_selection::infer::InferCtxtExt;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;

/// TyWrapper is a wrapper of rustc_middle::ty::Ty
#[derive(Clone, Copy, Eq, Debug)]
pub struct TyWrapper<'tcx> {
    ty: Ty<'tcx>,
}

impl<'tcx> TyWrapper<'tcx> {
    pub fn ty(&self) -> Ty<'tcx> {
        self.ty
    }

    pub fn into_ref(&self, tcx: TyCtxt<'tcx>) -> TyWrapper<'tcx> {
        Ty::new_ref(tcx, tcx.lifetimes.re_erased, self.ty, ty::Mutability::Not).into()
    }

    pub fn into_ref_mut(&self, tcx: TyCtxt<'tcx>) -> TyWrapper<'tcx> {
        Ty::new_ref(tcx, tcx.lifetimes.re_erased, self.ty, ty::Mutability::Mut).into()
    }

    pub fn transform(&self, kind: TransformKind, tcx: TyCtxt<'tcx>) -> TyWrapper<'tcx> {
        match kind {
            TransformKind::Ref(mutability) => {
                let ty = match mutability {
                    ty::Mutability::Not => self.into_ref(tcx),
                    ty::Mutability::Mut => self.into_ref_mut(tcx),
                };
                ty
            }
            _ => {
                todo!();
            }
        }
    }
}

impl<'tcx> From<Ty<'tcx>> for TyWrapper<'tcx> {
    fn from(ty: ty::Ty<'tcx>) -> TyWrapper<'tcx> {
        TyWrapper { ty }
    }
}

impl<'tcx> Into<Ty<'tcx>> for TyWrapper<'tcx> {
    fn into(self) -> Ty<'tcx> {
        self.ty
    }
}

impl PartialEq for TyWrapper<'_> {
    fn eq(&self, other: &Self) -> bool {
        eq_ty(self.ty, other.ty)
    }
}

impl Hash for TyWrapper<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        hash_ty(self.ty, state, &mut 0);
    }
}

fn eq_ty<'tcx>(lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> bool {
    match (lhs.kind(), rhs.kind()) {
        (ty::TyKind::Adt(adt_def1, generic_arg1), ty::TyKind::Adt(adt_def2, generic_arg2)) => {
            if adt_def1.did() != adt_def2.did() {
                return false;
            }
            for (arg1, arg2) in generic_arg1.iter().zip(generic_arg2.iter()) {
                match (arg1.kind(), arg2.kind()) {
                    (ty::GenericArgKind::Lifetime(_), ty::GenericArgKind::Lifetime(_)) => continue,
                    (ty::GenericArgKind::Type(ty1), ty::GenericArgKind::Type(ty2)) => {
                        if !eq_ty(ty1, ty2) {
                            return false;
                        }
                    }
                    (ty::GenericArgKind::Const(ct1), ty::GenericArgKind::Const(ct2)) => {
                        if ct1 != ct2 {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            true
        }
        (
            ty::TyKind::RawPtr(inner_ty1, mutability1),
            ty::TyKind::RawPtr(inner_ty2, mutability2),
        )
        | (
            ty::TyKind::Ref(_, inner_ty1, mutability1),
            ty::TyKind::Ref(_, inner_ty2, mutability2),
        ) => mutability1 == mutability2 && eq_ty(*inner_ty1, *inner_ty2),
        (ty::TyKind::Array(inner_ty1, _), ty::TyKind::Array(inner_ty2, _))
        | (ty::TyKind::Pat(inner_ty1, _), ty::TyKind::Pat(inner_ty2, _))
        | (ty::TyKind::Slice(inner_ty1), ty::TyKind::Slice(inner_ty2)) => {
            eq_ty(*inner_ty1, *inner_ty2)
        }
        (ty::TyKind::Tuple(tys1), ty::TyKind::Tuple(tys2)) => {
            if tys1.len() != tys2.len() {
                return false;
            }
            tys1.iter()
                .zip(tys2.iter())
                .all(|(ty1, ty2)| eq_ty(ty1, ty2))
        }
        _ => lhs == rhs,
    }
}

fn traverse_ty_with_lifetime<'tcx, F: Fn(ty::Region, usize)>(ty: Ty<'tcx>, no: &mut usize, f: &F) {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, generic_arg) => {
            for arg in generic_arg.iter() {
                match arg.kind() {
                    ty::GenericArgKind::Lifetime(lt) => {
                        *no = *no + 1;
                        f(lt, *no);
                    }
                    ty::GenericArgKind::Type(ty) => {
                        traverse_ty_with_lifetime(ty, no, f);
                    }
                    ty::GenericArgKind::Const(ct) => {}
                }
            }
        }

        ty::TyKind::RawPtr(inner_ty, mutability) => {
            traverse_ty_with_lifetime(*inner_ty, no, f);
        }

        ty::TyKind::Ref(region, inner_ty, mutability) => {
            *no = *no + 1;
            f(*region, *no);
            traverse_ty_with_lifetime(*inner_ty, no, f);
        }
        ty::TyKind::Array(inner_ty, _)
        | ty::TyKind::Pat(inner_ty, _)
        | ty::TyKind::Slice(inner_ty) => {
            traverse_ty_with_lifetime(*inner_ty, no, f);
        }
        ty::TyKind::Tuple(tys) => {
            for inner_ty in tys.iter() {
                traverse_ty_with_lifetime(inner_ty, no, f);
            }
        }
        _ => {
            unreachable!("unexpected ty kind");
        }
    }
}

// hashing Ty<'tcx>, but ignore the difference of lifetimes
fn hash_ty<'tcx, H: std::hash::Hasher>(ty: Ty<'tcx>, state: &mut H, no: &mut usize) {
    std::mem::discriminant(ty.kind()).hash(state);

    // hash the content
    match ty.kind() {
        ty::TyKind::Adt(adt_def, generic_arg) => {
            adt_def.did().hash(state);
            for arg in generic_arg.iter() {
                match arg.kind() {
                    ty::GenericArgKind::Lifetime(lt) => {
                        *no = *no + 1;
                        no.hash(state);
                    }
                    ty::GenericArgKind::Type(ty) => {
                        hash_ty(ty, state, no);
                    }
                    ty::GenericArgKind::Const(ct) => {
                        ct.hash(state);
                    }
                }
            }
        }

        ty::TyKind::RawPtr(inner_ty, mutability) => {
            mutability.hash(state);
            hash_ty(*inner_ty, state, no);
        }
        ty::TyKind::Ref(_, inner_ty, mutability) => {
            mutability.hash(state);
            *no = *no + 1;
            no.hash(state);
            hash_ty(*inner_ty, state, no);
        }
        ty::TyKind::Array(inner_ty, _) | ty::TyKind::Slice(inner_ty) => {
            hash_ty(*inner_ty, state, no);
        }
        ty::TyKind::Tuple(tys) => {
            for inner_ty in tys.iter() {
                hash_ty(inner_ty, state, no);
            }
        }
        _ => {
            ty.hash(state);
        }
    }
}

pub fn desc_ty_str<'tcx>(ty: Ty<'tcx>, no: &mut usize, tcx: TyCtxt<'tcx>) -> String {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, generic_arg) => {
            let mut ty_str = tcx.def_path_str(adt_def.did());
            if !generic_arg.is_empty() {
                ty_str += "<";
                ty_str += &generic_arg
                    .iter()
                    .map(|arg| match arg.kind() {
                        ty::GenericArgKind::Lifetime(lt) => {
                            let current_no = *no;
                            *no = *no + 1;
                            format!("'#{:?}", current_no)
                        }
                        ty::GenericArgKind::Type(ty) => desc_ty_str(ty, no, tcx),
                        ty::GenericArgKind::Const(ct) => format!("{:?}", ct),
                    })
                    .collect::<Vec<String>>()
                    .join(", ");
                ty_str += ">";
            }
            ty_str
        }

        ty::TyKind::RawPtr(inner_ty, mutability) => {
            format!(
                "*{} {}",
                mutability.ptr_str(),
                desc_ty_str(*inner_ty, no, tcx)
            )
        }
        ty::TyKind::Ref(_, inner_ty, mutability) => {
            let current_no = *no;
            *no = *no + 1;
            format!(
                "&'#{} {}{}",
                current_no,
                mutability.prefix_str(),
                desc_ty_str(*inner_ty, no, tcx)
            )
        }
        ty::TyKind::Array(inner_ty, len) => {
            format!("[{};{}]", desc_ty_str(*inner_ty, no, tcx), len)
        }

        ty::TyKind::Slice(inner_ty) => {
            format!("[{}]", desc_ty_str(*inner_ty, no, tcx))
        }
        ty::TyKind::Tuple(tys) => format!(
            "({})",
            tys.iter()
                .map(|ty| desc_ty_str(ty, no, tcx,))
                .collect::<Vec<String>>()
                .join(", "),
        ),
        ty::TyKind::Pat(inner_ty, _) => {
            unreachable!();
        }
        _ => format!("{:?}", ty),
    }
}

impl<'tcx> TyWrapper<'tcx> {
    pub fn desc_str(&self, tcx: TyCtxt<'tcx>) -> String {
        desc_ty_str(self.ty, &mut 0, tcx)
    }
}
