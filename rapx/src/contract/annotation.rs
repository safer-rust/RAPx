//! Contract annotations on functions and structs.

use crate::contract::{
    Property, PropertyArg, PropertyKind,
    attr::{collect_properties_from_named_attrs, is_rapx_named_attr, parse_rapx_attr},
    is_static_lifetime_ident,
};
use rustc_hir::{ItemKind, def_id::DefId};
use rustc_middle::ty::{self, EarlyParamRegion, GenericParamDefKind, Region, Ty, TyCtxt};

pub(crate) fn get_trait_method_requires<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
) -> Vec<Property<'tcx>> {
    let Some(assoc_item) = tcx.opt_associated_item(callee_def_id) else {
        return Vec::new();
    };
    let Some(trait_item_def_id) = assoc_item.trait_item_def_id() else {
        return Vec::new();
    };
    get_contract_from_annotation(tcx, trait_item_def_id)
}

/// Parses `requires` contracts from source-level RAPx annotations attached to a definition.
pub(crate) fn get_contract_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Property<'tcx>> {
    // Prefer HIR-level attrs for local defs (tool attributes visible),
    // fall back to get_all_attrs for external defs.
    if let Some(local_def_id) = def_id.as_local() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let hir_attrs = tcx.hir_attrs(hir_id);
        return collect_properties_from_named_attrs(tcx, hir_attrs, def_id, "requires", "requires");
    }

    let attrs = crate::compat::get_all_attrs(tcx, def_id);
    collect_properties_from_named_attrs(tcx, attrs, def_id, "requires", "requires")
}

/// Parses struct invariants from source-level RAPx annotations attached to a struct definition.
pub(crate) fn get_struct_invariants_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    struct_def_id: DefId,
    context_def_id: DefId,
) -> Vec<Property<'tcx>> {
    let Some(local_def_id) = struct_def_id.as_local() else {
        return Vec::new();
    };

    let item = tcx.hir_expect_item(local_def_id);
    if !matches!(item.kind, ItemKind::Struct(..)) {
        return Vec::new();
    }

    let mut invariants = collect_properties_from_named_attrs(
        tcx,
        crate::compat::get_all_attrs(tcx, struct_def_id),
        context_def_id,
        "invariant",
        "requires",
    );
    invariants.extend(collect_properties_from_named_attrs(
        tcx,
        crate::compat::get_all_attrs(tcx, struct_def_id),
        context_def_id,
        "invariant",
        "invariant",
    ));
    // A lifetime in a struct invariant (`Alive(ptr, 'a)`) names a lifetime on
    // the *struct*, so bind it here against the struct's own generics. Parsing
    // used `context_def_id` (the method), whose generics lack `'a`.
    for inv in &mut invariants {
        bind_alive_regions(tcx, struct_def_id, inv);
    }
    invariants
}

/// Bind `Alive(p, 'a)` region idents in a contract to `Region`s, resolving `'a`
/// against `def_id` (the item that declares `'a`: the struct for its
/// invariants, the function for its `requires`).
pub(crate) fn bind_alive_regions<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, property: &mut Property<'tcx>) {
    match property {
        Property::Atom(atom) => {
            if atom.kind == PropertyKind::Alive
                && let Some(PropertyArg::Ident(name)) = atom.args.get(1).cloned()
                && let Some(region) =
                    resolve_region_name(tcx, def_id, &name)
            {
                atom.args[1] = PropertyArg::Region(region);
            }
        }
        Property::And(and) => {
            for conjunct in &mut and.conjuncts {
                bind_alive_regions(tcx, def_id, conjunct);
            }
        }
        Property::Or(or) => {
            for disjunct in &mut or.disjuncts {
                bind_alive_regions(tcx, def_id, disjunct);
            }
        }
    }
}

/// Resolve a lifetime name from a contract (e.g. `"a"`, `"static_lifetime"`) to a
/// concrete `Region`. `name` is the raw ident, without the leading `'`.
pub(crate) fn resolve_region_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
) -> Option<Region<'tcx>> {
    if is_static_lifetime_ident(name) {
        return Some(tcx.lifetimes.re_static);
    }
    let ticked = format!("'{name}");
    let generics = tcx.generics_of(def_id);
    for param in &generics.own_params {
        if matches!(param.kind, GenericParamDefKind::Lifetime)
            && param.name.as_str() == ticked.as_str()
        {
            return Some(Region::new_early_param(
                tcx,
                EarlyParamRegion {
                    index: param.index,
                    name: param.name,
                },
            ));
        }
    }
    None
}


/// Resolve `Owning(self.field...)` invariants on a local returned struct to
/// field-index paths, without requiring a method `self` binding.
pub(crate) fn owning_field_paths_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    output: Ty<'tcx>,
) -> Vec<Vec<usize>> {
    let ty::Adt(adt, _) = output.kind() else {
        return Vec::new();
    };
    if !adt.did().is_local() || !adt.is_struct() {
        return Vec::new();
    }
    crate::compat::get_all_attrs(tcx, adt.did())
        .into_iter()
        .filter(|attr| is_rapx_named_attr(tcx, attr, "invariant"))
        .filter_map(|attr| {
            let text = crate::compat::attribute_to_string(tcx, attr);
            parse_rapx_attr(&text, "invariant").ok().flatten()
        })
        .filter(|property| property.tag == "Owning")
        .filter_map(|property| {
            let mut members = Vec::new();
            let mut expr = property.args.first()?;
            while let syn::Expr::Field(field) = expr {
                members.push(&field.member);
                expr = &field.base;
            }
            let syn::Expr::Path(root) = expr else { return None };
            if !root.path.is_ident("self") {
                return None;
            }
            let mut ty = output;
            let mut path = Vec::new();
            for member in members.into_iter().rev() {
                let ty::Adt(adt, args) = ty.kind() else { return None };
                let fields = &adt.non_enum_variant().fields;
                let index = match member {
                    syn::Member::Named(name) =>
                        fields.iter().position(|field| field.name.as_str() == name.to_string())?,
                    syn::Member::Unnamed(index) => index.index as usize,
                };
                let field = fields.iter().nth(index)?;
                path.push(index);
                ty = crate::util::mir_utils::field_ty(tcx, field, args);
            }
            Some(path)
        })
        .collect()
}
