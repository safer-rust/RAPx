//! Standard-library type-invariant generation.
//!
//! Type invariants are synthesized obligations that a value of a given type
//! must satisfy. Unlike user-written `#[rapx::invariant]` struct invariants,
//! these are generated automatically from the bundled `std-type-invariants.json`
//! database, keyed by a normalized type path (e.g. `core::num::NonZero`) or by
//! the built-in `[T]` slice key.
//!
//! The results feed the `type_invariants` field of a [`FunctionTarget`]
//! (see `super::target`), whose entry facts are synthesized by the VM's
//! `init_parameters` and re-proved at return by `VerifyDriver::verify_type_invariants`.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt};

use super::contract::{Property, PropertyArg, PropertyKind, json::AnyItem};

/// For each function parameter (and the return type), look up the type's
/// invariants from `std-type-invariants.json` and create preconditions.
pub(crate) fn build_type_invariants_from_params<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Property<'tcx>> {
    let db = crate::verify::contract::json::get_std_type_invariants();
    if db.is_empty() {
        return Vec::new();
    }

    let fn_sig = tcx.fn_sig(def_id).skip_binder();
    let inputs = fn_sig.inputs().skip_binder();
    let output = fn_sig.output().skip_binder();

    let mut results = Vec::new();

    // Use the existing signature parser for parameter names.
    let (param_names, _param_tys) = crate::helpers::name::parse_signature(tcx, def_id);

    // Add invariants for each parameter
    for (index, &param_ty) in inputs.iter().enumerate() {
        if param_ty.is_primitive() {
            continue;
        }
        let param_name = param_names.get(index).cloned().unwrap_or_default();
        let (type_path, elem_ty) = type_path_key(tcx, param_ty);
        collect_type_invariants(tcx, def_id, &db, &type_path, &param_name, elem_ty, &mut results);
    }

    // Also add invariants for the return type
    if !output.is_unit() && !output.is_primitive() {
        let (type_path, elem_ty) = type_path_key(tcx, output);
        collect_type_invariants(tcx, def_id, &db, &type_path, "return", elem_ty, &mut results);
    }

    results
}

/// Look up the type path in the DB and add instantiated invariants to `results`.
fn collect_type_invariants<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    db: &std::collections::HashMap<String, crate::verify::contract::json::TypeInvariantEntry>,
    type_path: &str,
    param_name: &str,
    elem_ty: Option<Ty<'tcx>>,
    results: &mut Vec<Property<'tcx>>,
) {
    if let Some(entry) = db.get(type_path) {
        for prop_entry in &entry.invariants {
            results.extend(instantiate_type_invariant(
                tcx,
                def_id,
                prop_entry,
                param_name,
                elem_ty,
            ));
        }
    }
    // Also try with common alloc/std prefixes
    for prefix in ["alloc::", "std::"] {
        let prefixed = format!("{prefix}{type_path}");
        if prefixed != type_path {
            if let Some(entry) = db.get(&prefixed) {
                for prop_entry in &entry.invariants {
                    results.extend(instantiate_type_invariant(
                        tcx,
                        def_id,
                        prop_entry,
                        param_name,
                        elem_ty,
                    ));
                }
            }
        }
    }
}

/// Create properties from a type invariant entry, substituting the parameter
/// name (and, for the slice entry, the element type). An entry with an `any`
/// field expands to a single disjunctive `Property::Or`; otherwise it yields
/// the properties denoted by its tag.
fn instantiate_type_invariant<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    entry: &crate::verify::contract::json::JsonProperty,
    param_name: &str,
    elem_ty: Option<Ty<'tcx>>,
) -> Vec<Property<'tcx>> {
    if let Some(disjuncts) = &entry.any {
        if disjuncts.len() < 2 {
            return Vec::new();
        }
        let mut or_disjuncts: Vec<Property<'tcx>> = Vec::with_capacity(disjuncts.len());
        for item in disjuncts {
            let mut group: Vec<Property<'tcx>> = Vec::new();
            match item {
                AnyItem::Single(e) => {
                    group.extend(instantiate_entry(tcx, def_id, e, param_name, elem_ty))
                }
                AnyItem::And(es) => {
                    for e in es {
                        group.extend(instantiate_entry(tcx, def_id, e, param_name, elem_ty));
                    }
                }
            }
            if !group.is_empty() {
                or_disjuncts.push(Property::conjunction(group));
            }
        }
        let mut property = Property::new_or(or_disjuncts);
        property.apply_kind(entry.kind.as_deref());
        return vec![property];
    }
    instantiate_entry(tcx, def_id, entry, param_name, elem_ty)
}

/// Placeholder type name substituted for the `$elem` token before parsing. The
/// JSON `$elem` is a bare type argument (e.g. `Align($self, $elem)`), and the
/// real element type — which can be a composite like `[T; N]` that has no
/// resolvable name — is injected afterwards by [`replace_ty_args`]. Any
/// primitive placeholder resolves cleanly through the name-based type parser.
const SLICE_ELEM_PLACEHOLDER: &str = "u8";

/// Instantiate a single (non-`any`) type invariant entry.
fn instantiate_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    entry: &crate::verify::contract::json::JsonProperty,
    param_name: &str,
    elem_ty: Option<Ty<'tcx>>,
) -> Vec<Property<'tcx>> {
    let mut uses_elem = false;
    let mut exprs: Vec<syn::Expr> = Vec::new();
    for arg_str in &entry.args {
        // Substitute the `$self` placeholder with the actual parameter name
        // (or "return"). `$elem` is a type argument: substitute a resolvable
        // placeholder and inject the real element type after parsing.
        let mut substituted = arg_str.replace("$self", param_name);
        if substituted.contains("$elem") {
            uses_elem = true;
            substituted = substituted.replace("$elem", SLICE_ELEM_PLACEHOLDER);
        }
        // Substitute struct field references like "0" → "param_name.0"
        let resolved = if is_numeric_field_access(&substituted) {
            format!("{}.{}", param_name, substituted)
        } else {
            substituted
        };
        match syn::parse_str::<syn::Expr>(&resolved) {
            Ok(expr) => exprs.push(expr),
            Err(_) => {
                rap_debug!(
                    "  [type-invariant] failed to parse arg '{}' for tag {}",
                    resolved,
                    entry.tag
                );
                return Vec::new();
            }
        }
    }
    if exprs.is_empty() {
        return Vec::new();
    }
    let mut property = Property::new(tcx, def_id, &entry.tag, &exprs);
    property.apply_kind(entry.kind.as_deref());
    if matches!(property.kind(), Some(PropertyKind::Unknown)) {
        return Vec::new();
    }
    if uses_elem {
        let Some(ty) = elem_ty else {
            // `$elem` was used but no element type is available: drop it.
            return Vec::new();
        };
        replace_ty_args(&mut property, ty);
    }
    vec![property]
}

/// Replace every type argument in a property tree with the slice element type.
///
/// The slice invariant's only type arguments are the `$elem` placeholders, so
/// this recovers the concrete element type (including composites such as
/// `[T; N]`) that the name-based JSON type parser cannot express.
fn replace_ty_args<'tcx>(property: &mut Property<'tcx>, ty: Ty<'tcx>) {
    match property {
        Property::Atom(atom) => {
            for arg in &mut atom.args {
                if let PropertyArg::Ty(t) = arg {
                    *t = ty;
                }
            }
        }
        Property::And(and) => {
            for conjunct in &mut and.conjuncts {
                replace_ty_args(conjunct, ty);
            }
        }
        Property::Or(or) => {
            for disjunct in &mut or.disjuncts {
                replace_ty_args(disjunct, ty);
            }
        }
    }
}

/// Check if a string looks like a numeric field access (e.g. "0").
fn is_numeric_field_access(s: &str) -> bool {
    let trimmed = s.trim();
    !trimmed.is_empty()
        && trimmed
            .split('.')
            .all(|part| !part.is_empty() && part.chars().all(|c| c.is_ascii_digit()))
}

/// Generate a normalised type path key for lookups in the type-invariants DB,
/// together with the element type for the built-in slice entry.
///
/// ADTs map to their def path (e.g. `core::num::NonZero`); `&[T]` / `&mut [T]`
/// slice references map to the built-in `[T]` key and carry their element type
/// (resolved via `$elem` during instantiation); anything else falls back to the
/// type's `Debug` representation.
fn type_path_key<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> (String, Option<Ty<'tcx>>) {
    match ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, _) => {
            // Build the canonical `crate::module::Type` path from the *defining*
            // crate, so the key is stable regardless of whether the type is
            // referenced through a `std` / `alloc` re-export (`def_path_str`
            // alone is crate-context dependent, e.g. `std::num::NonZero`).
            let def_id = adt_def.did();
            let crate_name = tcx.crate_name(def_id.krate);
            let path = tcx
                .def_path(def_id)
                .to_string_no_crate_verbose()
                .trim_start_matches("::")
                .to_string();
            (format!("{crate_name}::{path}"), None)
        }
        rustc_middle::ty::TyKind::Ref(_, inner, _) => match inner.kind() {
            rustc_middle::ty::TyKind::Slice(elem) => ("[T]".to_string(), Some(*elem)),
            _ => (format!("{ty:?}"), None),
        },
        _ => (format!("{ty:?}"), None),
    }
}
