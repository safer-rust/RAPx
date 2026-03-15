use itertools::Itertools;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::Ident;
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

fn join_path_with_ident(current_path: &str, ident: Ident) -> String {
    if current_path.is_empty() {
        ident.as_str().to_owned()
    } else {
        (current_path.to_string() + "::" + ident.as_str()).to_owned()
    }
}

impl<'tcx> PathResolver<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        PathResolver {
            tcx,
            path_map: HashMap::new(),
        }
    }

    fn build(&mut self, mod_id: DefId, current_path: String) {
        let childs = if mod_id.is_local() {
            self.tcx.module_children_local(mod_id.expect_local())
        } else {
            self.tcx.module_children(mod_id)
        };

        for child in childs {
            if !child.vis.is_public() {
                continue;
            }
            if let Some(did) = child.res.opt_def_id() {
                let path = join_path_with_ident(&current_path, child.ident);
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

    pub fn ty_str(&self, ty: Ty<'tcx>) -> String {
        match ty.kind() {
            TyKind::Adt(adt_def, args) => self.path_str_with_args(adt_def.did(), args),
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
            _ => ty.to_string(),
        }
    }

    pub fn path_str(&self, def_id: DefId) -> String {
        self.path_str_with_args(def_id, ty::GenericArgs::identity_for_item(self.tcx, def_id))
    }

    pub fn path_str_with_args(&self, def_id: DefId, args: ty::GenericArgsRef<'tcx>) -> String {
        // `{assoc_path}::{item_name}`
        if let Some((assoc_id, kind)) = self.tcx.assoc_parent(def_id) {
            rap_trace!("assoc item: {:?} => {:?}", assoc_id, kind);
            // the number of generic of assoc parent
            let num_generic = self.tcx.generics_of(assoc_id).own_params.len();

            let (parent_args, own_args) = args.split_at(num_generic);

            let parent_path_str = match kind {
                // Trait Impl
                DefKind::Impl { of_trait: true } => {
                    let trait_ref = self
                        .tcx
                        .impl_trait_ref(assoc_id)
                        .instantiate(self.tcx, parent_args);

                    let self_ty_str = self.ty_str(trait_ref.self_ty());
                    let trait_str = self.non_assoc_path_str(trait_ref.def_id);
                    if trait_ref.args.len() > 1 {
                        format!(
                            "<{} as {}{}>",
                            self_ty_str,
                            trait_str,
                            self.generic_args_str(&trait_ref.args[1..])
                        )
                    } else {
                        format!("<{} as {}>", self_ty_str, trait_str)
                    }
                }
                // inherent impl
                DefKind::Impl { of_trait: false } => {
                    let self_ty = self
                        .tcx
                        .type_of(assoc_id)
                        .instantiate(self.tcx, parent_args);
                    self.ty_str(self_ty)
                }
                // Trait
                DefKind::Trait => {
                    let self_ty = parent_args[0].expect_ty();
                    let self_ty_str = self.ty_str(self_ty);
                    let trait_str = self.non_assoc_path_str(assoc_id);
                    if parent_args.len() > 1 {
                        format!(
                            "<{} as {}{}>",
                            self_ty_str,
                            trait_str,
                            self.generic_args_str(&parent_args[1..])
                        )
                    } else {
                        format!("<{} as {}>", self_ty_str, trait_str)
                    }
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

            if own_args.len() > 0 {
                format!(
                    "{}::{}::{}",
                    parent_path_str,
                    self.tcx.item_name(def_id),
                    self.generic_args_str(own_args)
                )
            } else {
                format!("{}::{}", parent_path_str, self.tcx.item_name(def_id))
            }
        } else {
            if args.len() > 0 {
                format!(
                    "{}::{}",
                    self.non_assoc_path_str(def_id),
                    self.generic_args_str(args)
                )
            } else {
                format!("{}", self.non_assoc_path_str(def_id))
            }
        }
    }

    pub fn generic_arg_str(&self, arg: ty::GenericArg<'tcx>) -> String {
        match arg.kind() {
            ty::GenericArgKind::Lifetime(_) => "'_".to_string(),
            ty::GenericArgKind::Type(ty) => self.ty_str(ty),
            ty::GenericArgKind::Const(const_) => format!("{}", const_),
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
}
