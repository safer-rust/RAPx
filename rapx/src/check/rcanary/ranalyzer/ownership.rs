use std::{collections::HashSet, fmt::Debug};
use z3::ast;

use rustc_middle::ty::Ty;

use crate::analysis::heap_ownership::default::TyWithIndex;

#[derive(Clone, Debug)]
#[derive(Default)]
pub struct Taint<'tcx> {
    set: HashSet<TyWithIndex<'tcx>>,
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
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[derive(Default)]
pub enum IntraVar<'z3> {
    #[default]
    Declared,
    Init(ast::BV<'z3>),
    Unsupported,
}


impl<'z3> IntraVar<'z3> {
    pub fn is_declared(&self) -> bool {
        matches!(self, IntraVar::Declared)
    }

    pub fn is_init(&self) -> bool {
        matches!(self, IntraVar::Init(_))
    }

    pub fn is_unsupported(&self) -> bool {
        matches!(self, IntraVar::Unsupported)
    }

    pub fn extract(&self) -> ast::BV<'z3> {
        match self {
            IntraVar::Init(ast) => ast.clone(),
            _ => unreachable!(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
#[derive(Default)]
pub enum ContextTypeOwner<'tcx> {
    Owned { kind: OwnerKind, ty: Ty<'tcx> },
    #[default]
    Unowned,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum OwnerKind {
    Instance,
    Reference,
    Pointer,
}


impl<'tcx> ContextTypeOwner<'tcx> {
    pub fn is_owned(&self) -> bool {
        match self {
            ContextTypeOwner::Owned { .. } => true,
            ContextTypeOwner::Unowned => false,
        }
    }
}
