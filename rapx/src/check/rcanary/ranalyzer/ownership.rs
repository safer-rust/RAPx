use std::{collections::HashSet, fmt::Debug};
use z3::ast;

use rustc_middle::ty::Ty;

use crate::analysis::core::ownedheap_analysis::default::TyWithIndex;

#[derive(Clone, Debug)]
pub struct Taint<'tcx> {
    set: HashSet<TyWithIndex<'tcx>>,
}

impl<'tcx> Default for Taint<'tcx> {
    fn default() -> Self {
        Self {
            set: HashSet::default(),
        }
    }
}

impl<'tcx> Taint<'tcx> {
    pub fn is_untainted(&self) -> bool {
        self.set.is_empty()
    }

    pub fn is_tainted(&self) -> bool {
        !self.set.is_empty()
    }

    pub fn contains(&self, k: &TyWithIndex<'tcx>) -> bool {
        self.set.contains(k)
    }

    pub fn insert(&mut self, k: TyWithIndex<'tcx>) {
        self.set.insert(k);
    }

    pub fn set(&self) -> &HashSet<TyWithIndex<'tcx>> {
        &self.set
    }

    pub fn set_mut(&mut self) -> &mut HashSet<TyWithIndex<'tcx>> {
        &mut self.set
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum IntraVar<'ctx> {
    Declared,
    Init(ast::BV<'ctx>),
    Unsupported,
}

impl<'ctx> Default for IntraVar<'ctx> {
    fn default() -> Self {
        Self::Declared
    }
}

impl<'ctx> IntraVar<'ctx> {
    pub fn is_declared(&self) -> bool {
        match *self {
            IntraVar::Declared => true,
            _ => false,
        }
    }

    pub fn is_init(&self) -> bool {
        match *self {
            IntraVar::Init(_) => true,
            _ => false,
        }
    }

    pub fn is_unsupported(&self) -> bool {
        match *self {
            IntraVar::Unsupported => true,
            _ => false,
        }
    }

    pub fn extract(&self) -> ast::BV<'ctx> {
        match self {
            IntraVar::Init(ast) => ast.clone(),
            _ => unreachable!(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum ContextTypeOwner<'tcx> {
    Owned { kind: OwnerKind, ty: Ty<'tcx> },
    Unowned,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum OwnerKind {
    Instance,
    Reference,
    Pointer,
}

impl<'tcx> Default for ContextTypeOwner<'tcx> {
    fn default() -> Self {
        Self::Unowned
    }
}

impl<'tcx> ContextTypeOwner<'tcx> {
    pub fn is_owned(&self) -> bool {
        match self {
            ContextTypeOwner::Owned { .. } => true,
            ContextTypeOwner::Unowned => false,
        }
    }

    pub fn get_ty(&self) -> Option<Ty<'tcx>> {
        match *self {
            ContextTypeOwner::Owned { ty, .. } => Some(ty),
            ContextTypeOwner::Unowned => None,
        }
    }
}
