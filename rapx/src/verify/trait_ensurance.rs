//! Targets and obligations collected from unsafe trait implementations.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::contract::{Property, PropertyArg, PropertyKind};
use crate::contract::annotation::get_struct_invariants_from_annotation;

/// Obligations from an unsafe trait implementation.
///
/// `Send` and `Sync` use type-level obligations. Other unsafe traits use
/// method-level `ensures` contracts.
#[derive(Clone)]
pub(crate) struct TraitEnsurance<'tcx> {
    /// The trait being implemented.
    pub def_id: DefId,

    /// Implementation block, including its generic bounds.
    pub impl_def_id: DefId,

    /// Implementing type, when it resolves to an ADT.
    pub self_ty_def_id: Option<DefId>,

    /// Type-level or method-level obligations.
    pub kind: TraitEnsuranceKind<'tcx>,
}

/// What a [`TraitEnsurance`] must verify.
#[derive(Clone)]
pub(crate) enum TraitEnsuranceKind<'tcx> {
    /// `Send` or `Sync` obligations from the bundled trait template.
    Marker(MarkerTraitKind, Vec<Property<'tcx>>),

    /// Unsafe trait `ensures` contracts grouped by method name.
    Unsafe(Vec<(String, Vec<Property<'tcx>>)>),
}

/// Which marker trait an `unsafe impl` is claiming safety for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum MarkerTraitKind {
    Send,
    Sync,
}

/// Resolve whether an `unsafe impl` is implementing the `Send`/`Sync` marker trait.
pub(super) fn marker_trait_kind(tcx: TyCtxt<'_>, trait_def_id: DefId) -> Option<MarkerTraitKind> {
    if tcx.get_diagnostic_item(rustc_span::sym::Send) == Some(trait_def_id) {
        Some(MarkerTraitKind::Send)
    } else if tcx.get_diagnostic_item(rustc_span::sym::Sync) == Some(trait_def_id) {
        Some(MarkerTraitKind::Sync)
    } else {
        None
    }
}

/// Generate the type-level `ensures` obligations for a marker-trait impl from
/// the bundled `std-trait.json` template, substituting `ty:Self` with
/// the implementing type.
pub(super) fn build_marker_trait_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_ty_def_id: Option<DefId>,
    trait_kind: MarkerTraitKind,
) -> Vec<Property<'tcx>> {
    let Some(self_ty_def_id) = self_ty_def_id else {
        return Vec::new();
    };
    let self_ty = tcx.type_of(self_ty_def_id).skip_binder();

    let trait_def_id = match trait_kind {
        MarkerTraitKind::Send => tcx.get_diagnostic_item(rustc_span::sym::Send),
        MarkerTraitKind::Sync => tcx.get_diagnostic_item(rustc_span::sym::Sync),
    };
    let Some(trait_def_id) = trait_def_id else {
        return Vec::new();
    };

    let templates = crate::contract::json::query_trait_ensures(tcx, trait_def_id);
    let mut obligations = Vec::new();
    for entry in templates {
        if let Some(prop) = build_type_atom(tcx, self_ty_def_id, &entry, self_ty) {
            obligations.push(prop);
        }
    }
    obligations
}

/// Build a single type-level obligation from a `std-trait.json` entry,
/// substituting `ty:Self` with `self_ty`.  Supports the `any` disjunction and
/// falls back to named compound properties (`expand_compound`) for tags that are
/// not built-in primitives.
fn build_type_atom<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    entry: &crate::contract::json::JsonProperty,
    self_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Property<'tcx>> {
    if let Some(items) = &entry.any {
        let disjuncts: Vec<Property<'tcx>> = items
            .iter()
            .filter_map(|item| match item {
                crate::contract::json::AnyItem::Single(e) => {
                    build_type_atom(tcx, def_id, e, self_ty)
                }
                crate::contract::json::AnyItem::And(es) => {
                    let conjuncts: Vec<Property<'tcx>> = es
                        .iter()
                        .filter_map(|e| build_type_atom(tcx, def_id, e, self_ty))
                        .collect();
                    if conjuncts.is_empty() {
                        None
                    } else {
                        Some(Property::new_and(conjuncts))
                    }
                }
            })
            .collect();
        return if disjuncts.is_empty() {
            None
        } else {
            Some(Property::new_or(disjuncts))
        };
    }

    match entry.tag.as_str() {
        "ContainNoType" => {
            let mut args = vec![PropertyArg::Ty(self_ty)];
            args.extend(
                entry.args[1..]
                    .iter()
                    .map(|s| PropertyArg::Ident(s.strip_prefix("ty:").unwrap_or(s).to_string())),
            );
            Some(Property::new_atom(PropertyKind::ContainNoType, args))
        }
        "NoRawPtr" => Some(Property::new_atom(
            PropertyKind::NoRawPtr,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "NoInternalMut" => Some(Property::new_atom(
            PropertyKind::NoInternalMut,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "UniInternalMut" => Some(Property::new_atom(
            PropertyKind::UniInternalMut,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "AtomicUpdate" => Some(Property::new_atom(
            PropertyKind::AtomicUpdate,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "RefSend" => Some(Property::new_atom(
            PropertyKind::RefSend,
            vec![PropertyArg::Ty(self_ty)],
        )),
        // Fall back to a named compound property (e.g. `TamedRawPtr` defined in
        // `std-compound-properties.rs`).  The `ty:Self` placeholder is normalized
        // to `Self` and resolved by the compound's `Ty` parameter; a `Ptr`
        // parameter not supplied by the JSON template is filled in from the
        // struct's own `Allocated`/`Owning` invariant field.
        _ => {
            let mut exprs: Vec<syn::Expr> = entry
                .args
                .iter()
                .filter_map(|s| {
                    let normalized = crate::contract::json::normalize_json_contract_arg(s);
                    syn::parse_str::<syn::Expr>(&normalized).ok()
                })
                .collect();
            if exprs.len() != entry.args.len() {
                return None;
            }

            if let Some(spec) = crate::contract::compound::find_compound(def_id.krate, &entry.tag) {
                for i in exprs.len()..spec.param_tys.len() {
                    if spec.param_tys.get(i).map(|s| s.as_str()) != Some("Ptr") {
                        return None;
                    }
                    let field = extract_tamed_field(tcx, def_id)?;
                    let Ok(e) = syn::parse_str::<syn::Expr>(&field) else {
                        return None;
                    };
                    exprs.push(e);
                }
            }

            match crate::contract::compound::expand_compound(tcx, def_id, &entry.tag, &exprs) {
                Some(mut props) if !props.is_empty() => {
                    // A compound body expands into one property per conjunct, each
                    // tagged with the compound's origin.  Hoist that origin onto the
                    // combined node so the report shows `Name(args)` once instead of
                    // `And(Name, Name, Name)`.
                    let origin = props.first().and_then(|p| p.origin()).cloned();
                    for p in &mut props {
                        p.clear_origin();
                    }
                    let mut combined = Property::conjunction(props);
                    if let Some(o) = origin {
                        combined.set_origin(o.name, o.args, o.meaning);
                    }
                    Some(combined)
                }
                _ => None,
            }
        }
    }
}

/// The raw-pointer field name a struct declares via `#[rapx::invariant(Allocated(field))]`
/// or `#[rapx::invariant(Owning(field))]`, used to bind a `TamedRawPtr` compound's
/// `Ptr` parameter.
fn extract_tamed_field<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<String> {
    let invariants = get_struct_invariants_from_annotation(tcx, def_id, def_id);
    invariants
        .iter()
        .find(|p| {
            matches!(
                p.kind(),
                Some(PropertyKind::Allocated) | Some(PropertyKind::Owning)
            )
        })
        .and_then(|p| p.args().first())
        .and_then(|a| crate::contract::place::field_name_from_arg(tcx, def_id, a))
}
