use super::graph::ApiDependencyGraph;
use super::graph::{DepEdge, DepNode};
use super::is_def_id_public;
use crate::analysis::core::api_dependency::mono;
use crate::{rap_debug, rap_trace};
use rustc_hir::LangItem;
use rustc_hir::{
    BodyId, BodyOwnerKind, FnDecl,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
};
use rustc_middle::ty::{self, FnSig, ParamEnv, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::io::Write;

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Hash)]
pub struct Config {
    pub ignore_const_generic: bool,
    pub include_unsafe: bool,
    pub include_drop: bool,
    pub include_generic: bool,
    pub pub_only: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            pub_only: true,
            ignore_const_generic: true,
            include_unsafe: false,
            include_drop: false,
            include_generic: true,
        }
    }
}

pub struct FnVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    apis: Vec<DefId>,
    generic_apis: Vec<DefId>,
    config: Config,
}

impl<'tcx> FnVisitor<'tcx> {
    pub fn new(config: Config, tcx: TyCtxt<'tcx>) -> FnVisitor<'tcx> {
        FnVisitor {
            tcx,
            apis: Vec::new(),
            generic_apis: Vec::new(),
            config,
        }
    }

    pub fn count_api(&self) -> usize {
        self.apis.len()
    }

    pub fn count_generic_api(&self) -> usize {
        self.generic_apis.len()
    }

    pub fn non_generic_apis(&self) -> &[DefId] {
        &self.apis
    }

    pub fn generic_apis(&self) -> &[DefId] {
        &self.generic_apis
    }

    pub fn write_funcs<T: Write>(&self, f: &mut T) {
        for id in &self.apis {
            write!(f, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }
}

pub fn has_const_generics(generics: &ty::Generics, tcx: TyCtxt<'_>) -> bool {
    if generics
        .own_params
        .iter()
        .any(|param| matches!(param.kind, ty::GenericParamDefKind::Const { .. }))
    {
        return true;
    }

    if let Some(parent_def_id) = generics.parent {
        let parent = tcx.generics_of(parent_def_id);
        has_const_generics(parent, tcx)
    } else {
        false
    }
}

fn is_drop_impl(tcx: TyCtxt<'_>, fn_did: DefId) -> bool {
    if let Some(impl_id) = tcx.trait_impl_of_assoc(fn_did) {
        let trait_did = tcx.impl_trait_id(impl_id);
        if tcx.is_lang_item(trait_did, LangItem::Drop) {
            return true;
        }
    }
    false
}

impl<'tcx> Visitor<'tcx> for FnVisitor<'tcx> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        _fd: &'v FnDecl<'v>,
        _b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        let fn_did = id.to_def_id();
        let generics = self.tcx.generics_of(fn_did);
        rap_trace!(
            "visit fn: {:?} (path: {}), generics: {:?}, span: {:?}",
            fn_did,
            self.tcx.def_path_str(fn_did),
            generics,
            span,
        );

        if self.tcx.def_path_str(fn_did).ends_with("dummy") && self.tcx.def_span(fn_did).is_dummy()
        {
            rap_trace!("skip rustc dummy fn");
            return;
        }

        if self.config.pub_only && !is_def_id_public(fn_did, self.tcx) {
            rap_trace!("skip for non-public");
            return;
        }

        if !self.config.include_drop && is_drop_impl(self.tcx, fn_did) {
            rap_trace!("skip drop impl");
            return;
        }

        let is_generic = generics.requires_monomorphization(self.tcx);

        // if config.resolve_generic is false, skip all generic functions
        if !self.config.include_generic && is_generic {
            rap_trace!("skip generic fn");
            return;
        }

        // if config.ignore_const_generic is true,
        // skip functions with const generics
        if self.config.ignore_const_generic && has_const_generics(generics, self.tcx) {
            rap_trace!("skip const generic fn");
            return;
        }

        if !self.config.include_unsafe && fk.header().unwrap().safety().is_unsafe() {
            rap_trace!("skip unsafe fn");
            return;
        }

        if is_generic {
            self.generic_apis.push(fn_did);
        } else {
            self.apis.push(fn_did);
        }
    }
}
