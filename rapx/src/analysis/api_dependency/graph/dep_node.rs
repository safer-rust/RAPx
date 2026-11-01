use std::hash::Hash;

use super::ty_wrapper::TyWrapper;
use crate::compat::GenericArgsRef;
use rustc_middle::ty::{self, Ty, TyCtxt};

use rustc_hir::def_id::DefId;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum DepNode<'tcx> {
    Api(DefId, GenericArgsRef<'tcx>),
    Ty(TyWrapper<'tcx>),
}

impl<'tcx> DepNode<'tcx> {
    pub fn api(id: DefId, args: GenericArgsRef<'tcx>) -> DepNode<'tcx> {
        DepNode::Api(id, args)
    }
    pub fn ty(ty: Ty<'tcx>) -> DepNode<'tcx> {
        DepNode::Ty(TyWrapper::from(ty))
    }
    pub fn is_ty(&self) -> bool {
        matches!(self, DepNode::Ty(_))
    }
    pub fn is_api(&self) -> bool {
        matches!(self, DepNode::Api(..))
    }

    pub fn as_ty(&self) -> Option<TyWrapper<'tcx>> {
        match self {
            DepNode::Ty(ty) => Some(*ty),
            _ => None,
        }
    }

    pub fn expect_ty(&self) -> TyWrapper<'tcx> {
        match self {
            DepNode::Ty(ty) => *ty,
            _ => panic!("{self:?} is not a ty"),
        }
    }

    pub fn expect_api(&self) -> (DefId, GenericArgsRef<'tcx>) {
        match self {
            DepNode::Api(did, args) => (*did, *args),
            _ => {
                panic!("{self:?} is not an api")
            }
        }
    }

    pub fn desc_str(&self, tcx: TyCtxt<'tcx>) -> String {
        match self {
            DepNode::Api(def_id, args) => tcx.def_path_str_with_args(*def_id, *args),
            DepNode::Ty(ty) => ty.desc_str(tcx),
        }
    }
}
