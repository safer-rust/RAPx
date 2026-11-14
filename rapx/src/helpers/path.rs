#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use crate::compat::GenericArgsRef;
use itertools::Itertools;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use std::collections::HashMap;

/// A utility to resolve the actual visible path for re-export items.
pub struct PathResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    path_map: HashMap<DefId, String>,
}

pub fn get_path_resolver<'tcx>(tcx: TyCtxt<'tcx>) -> PathResolver<'tcx> {
    let mut resolver = PathResolver::new(tcx);
    resolver.build(LOCAL_CRATE.as_def_id(), String::new());
    resolver
}

fn join_path_with_double_colon(parts: &[&str]) -> String {
    parts.iter().filter(|s| !s.is_empty()).join("::")
}

impl<'tcx> PathResolver<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        PathResolver {
            tcx,
            path_map: HashMap::new(),
        }
    }

    fn build(&mut self, mod_id: DefId, current_path: String) {
        rap_trace!("enter module: {:?}, path: {}", mod_id, current_path);
        let childs = if mod_id.is_local() {
            self.tcx.module_children_local(mod_id.expect_local())
        } else {
            self.tcx.module_children(mod_id)
        };

        for child in childs {
            rap_trace!(
                "processing child: {:?}, ident = {}",
                child.res,
                child.ident.as_str()
            );
            if !child.vis.is_public() || child.ident.as_str() == "_" {
                continue;
            }
            if let Some(did) = child.res.opt_def_id() {
                let path = join_path_with_double_colon(&[&current_path, child.ident.as_str()]);
                self.path_map.entry(did).or_insert(path.clone());
                if self.tcx.def_kind(did).is_module_like() {
                    self.build(did, path);
                }
            }
        }
    }

    fn non_assoc_path_str(&self, def_id: DefId) -> String {
        match self.path_map.get(&def_id) {
            Some(path) => path.clone(),
            None => {
                // if def_id is from local crate, but we cannot find it in path_map,
                // report this error.
                if def_id.is_local() {
                    rap_error!(
                        "[PathResolver] cannot find path for {:?}, fallback to self.tcx.def_path_str",
                        def_id
                    );
                }
                self.tcx.def_path_str(def_id)
            }
        }
    }

    pub fn path_exists(&self, did: DefId) -> bool {
        let Some((assoc_id, kind)) = self.tcx.assoc_parent(did) else {
            // check non associated item
            return did.is_local() && self.path_map.contains_key(&did)
            // for did from other crate, we rely on tcx.visibility, 
            // which is not 100% accurate, but should be good enough in most cases.
                || !did.is_local() && self.tcx.visibility(did).is_public();
        };

        if !self.tcx.visibility(did).is_public() {
            return false;
        }

        match kind {
            DefKind::Impl { .. } => {
                let self_ty = self
                    .tcx
                    .type_of(assoc_id)
                    .instantiate_identity()
                    .skip_norm_wip();
                match self_ty.kind() {
                    // Theoretically, we need to check visibility of generic args.
                    // However, it is a bit complicated and we currently do not consider it.
                    TyKind::Adt(adt_def, _) => self.path_exists(adt_def.did()),
                    _ => true,
                }
            }
            DefKind::Trait => self.path_exists(assoc_id),
            _ => panic!(
                "unexpected parent kind: {:?} for assoc item: {:?}",
                kind, did
            ),
        }
    }

    pub fn ty_str(&self, ty: Ty<'tcx>) -> String {
        match ty.kind() {
            TyKind::Adt(adt_def, args) => self.path_str_with_args(adt_def.did(), *args),
            TyKind::Array(inner_ty, const_) => {
                format!("[{};{}]", self.ty_str(*inner_ty), const_)
            }
            TyKind::Tuple(tys) => {
                format!("({})", tys.iter().map(|ty| self.ty_str(ty)).join(", "))
            }
            TyKind::Ref(region, inner_ty, mutability) => {
                format!(
                    "&{} {}{}",
                    region,
                    mutability.prefix_str(),
                    self.ty_str(*inner_ty)
                )
            }
            TyKind::RawPtr(inner_ty, mutability) => {
                format!("*{} {}", mutability.ptr_str(), self.ty_str(*inner_ty))
            }
            TyKind::Slice(inner_ty) => {
                format!("[{}]", self.ty_str(*inner_ty))
            }
            #[cfg(rapx_alias_ty_structured_kind)]
            TyKind::Alias(is_rigid, alias_ty) => match alias_ty.kind {
                ty::AliasTyKind::Projection { def_id } => {
                    self.path_str_with_args(def_id, alias_ty.args)
                }
                ty::AliasTyKind::Opaque { .. } => {
                    let ty_str = alias_ty.to_ty(self.tcx, *is_rigid).to_string();
                    rap_warn!(
                        "encounter opaque type {}, type string might be private",
                        ty_str
                    );
                    ty_str
                }
                kind => {
                    panic!(
                        "unexpected alias kind: {:?} for alias_ty: {:?}",
                        kind, alias_ty
                    );
                }
            },
            #[cfg(not(rapx_alias_ty_structured_kind))]
            TyKind::Alias(alias_kind, alias_ty) => match alias_kind {
                ty::AliasTyKind::Projection => {
                    self.path_str_with_args(alias_ty.def_id, alias_ty.args)
                }
                ty::AliasTyKind::Opaque => {
                    let ty_str = alias_ty.to_ty(self.tcx).to_string();
                    rap_warn!(
                        "encounter opaque type {}, type string might be private",
                        ty_str
                    );
                    ty_str
                }
                kind => {
                    panic!(
                        "unexpected alias kind: {:?} for alias_ty: {:?}",
                        kind, alias_ty
                    );
                }
            },
            _ => ty.to_string(),
        }
    }

    #[allow(unused)]
    pub fn path_str(&self, def_id: DefId) -> String {
        self.path_str_with_args(def_id, ty::GenericArgs::identity_for_item(self.tcx, def_id))
    }

    pub fn path_str_with_args(&self, def_id: DefId, args: GenericArgsRef<'tcx>) -> String {
        // `{assoc_path}::{item_name}`
        if let Some((assoc_id, kind)) = self.tcx.assoc_parent(def_id) {
            rap_trace!("assoc item: {:?} => {:?}", assoc_id, kind);
            // the number of generic of assoc parent
            let num_generic = self.tcx.generics_of(assoc_id).own_params.len();

            let (parent_args, own_args) = args.as_slice().split_at(num_generic);

            let parent_path_str = match kind {
                // Trait Impl
                DefKind::Impl { of_trait: true } => {
                    let trait_ref = self
                        .tcx
                        .impl_trait_ref(assoc_id)
                        .instantiate(self.tcx, parent_args);

                    let trait_ref = trait_ref.skip_norm_wip();

                    self.qualified_path_str(
                        trait_ref.self_ty(),
                        trait_ref.def_id,
                        &trait_ref.args.as_slice()[1..],
                    )
                }
                // inherent impl
                DefKind::Impl { of_trait: false } => {
                    let self_ty = self
                        .tcx
                        .type_of(assoc_id)
                        .instantiate(self.tcx, parent_args);
                    let self_ty = self_ty.skip_norm_wip();
                    self.ty_str(self_ty)
                }
                // Trait
                DefKind::Trait => {
                    self.qualified_path_str(parent_args[0].expect_ty(), assoc_id, &parent_args[1..])
                }
                _ => {
                    unreachable!(
                        "unexpected assoc parent: {:?} => {:?}, def_id: {:?}, path: {:?}",
                        assoc_id,
                        kind,
                        def_id,
                        self.tcx.def_path_str_with_args(def_id, args)
                    );
                }
            };

            let args_str = self.non_syn_generic_args_str(def_id, own_args);

            join_path_with_double_colon(&[
                &parent_path_str,
                self.tcx.item_name(def_id).as_str(),
                &args_str,
            ])
        } else {
            // non assoc item
            let path_str = self.non_assoc_path_str(def_id);
            let args_str = self.non_syn_generic_args_str(def_id, args.as_slice());
            join_path_with_double_colon(&[path_str.as_str(), args_str.as_str()])
        }
    }

    pub fn generic_arg_str(&self, arg: ty::GenericArg<'tcx>) -> String {
        match arg.kind() {
            ty::GenericArgKind::Lifetime(_) => "'_".to_string(),
            ty::GenericArgKind::Type(ty) => self.ty_str(ty),
            ty::GenericArgKind::Const(const_) => format!("{}", const_),
        }
    }

    /// Format `<Self as Trait<args>>` for a trait impl or trait-associated item.
    fn qualified_path_str(
        &self,
        self_ty: Ty<'tcx>,
        trait_id: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> String {
        let self_ty_str = self.ty_str(self_ty);
        let trait_str = self.non_assoc_path_str(trait_id);
        if args.is_empty() {
            format!("<{} as {}>", self_ty_str, trait_str)
        } else {
            format!(
                "<{} as {}{}>",
                self_ty_str,
                trait_str,
                self.generic_args_str(args)
            )
        }
    }

    fn generic_args_str(&self, generic_args: &[ty::GenericArg<'tcx>]) -> String {
        format!(
            "<{}>",
            generic_args
                .iter()
                .map(|arg| self.generic_arg_str(*arg))
                .join(", ")
        )
    }

    fn non_syn_generic_args_str(&self, def_id: DefId, args: &[ty::GenericArg<'tcx>]) -> String {
        let defs = self.tcx.generics_of(def_id).own_params.as_slice();

        assert!(defs.len() == args.len());

        let non_syn_args = args
            .iter()
            .zip(defs.iter())
            .filter_map(|(arg, param)| {
                if param.kind.is_synthetic() {
                    None
                } else {
                    Some(*arg)
                }
            })
            .collect_vec();

        // No suffix for empty generic args, e.g. render `foo` instead of `foo::<>`.
        if non_syn_args.is_empty() {
            String::new()
        } else {
            self.generic_args_str(&non_syn_args)
        }
    }
}
