//! Assemble a safety tag into a [`Property`] via the declarative spec table.
//!
//! `Property::new` looks up `spec::SPECS`, dispatches on the tag's `BuildKind`,
//! and resolves arguments positionally. `Property::parse_list` is the shared
//! entry point for all front-ends, including the `any(...)` combinator.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use quote::ToTokens;
use syn::Expr;

use crate::helpers::name::access_ident_recursive;

use super::types::*;
use super::spec;

impl<'tcx> Property<'tcx> {
    /// Parse a property from the declaration table, dispatching on the tag's
    /// assembly strategy.
    fn parse_from_spec(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        spec: &spec::PropertySpec,
        exprs: &[Expr],
    ) -> Self {
        let mut prop = match spec.build {
            spec::BuildKind::Uniform => Self::build_uniform(tcx, def_id, spec, exprs),
            spec::BuildKind::Size => Self::build_size(tcx, def_id, exprs),
            spec::BuildKind::Allocated => Self::build_allocated(tcx, def_id, exprs),
            spec::BuildKind::InBound => Self::build_inbound(tcx, def_id, exprs),
            spec::BuildKind::NonOverlap => Self::build_nonoverlap(tcx, def_id, exprs),
            spec::BuildKind::ValidNum => Self::build_validnum(tcx, def_id, exprs),
            spec::BuildKind::Pinned => Self::build_pinned(tcx, def_id, exprs),
            spec::BuildKind::SplitTransmute => Self::build_split_transmute(tcx, def_id, exprs),
            spec::BuildKind::Targets => Self::build_targets(spec, tcx, def_id, exprs),
            spec::BuildKind::TobeSpecified => Self::new_simple(PropertyKind::Unknown),
        };
        // Apply the spec-declared `ContractKind` centrally, so `Hazard` /
        // `Option_` tags keep their kind regardless of build strategy (not just
        // for `BuildKind::Targets`).
        prop.set_contract_kind(spec.contract_kind);
        prop
    }

    /// Resolve a single positional argument according to its declared role.
    ///
    /// Returns `None` when a `Ty` argument cannot be resolved, so the caller
    /// degrades the whole property to `Unknown` instead of silently
    /// substituting the `never` type (which would make `Align`/`Typed` trivially
    /// provable).
    fn resolve_arg(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        tag: &str,
        arg_kind: spec::ArgKind,
        expr: &Expr,
    ) -> Option<PropertyArg<'tcx>> {
        match arg_kind {
            spec::ArgKind::Target => Some(super::resolve::parse_target_arg(tcx, def_id, expr)),
            spec::ArgKind::Ty => {
                super::resolve::parse_type(tcx, def_id, expr, tag).map(PropertyArg::Ty)
            }
            spec::ArgKind::Expr => {
                let text = expr.to_token_stream().to_string();
                Some(PropertyArg::Expr(super::pest_conv::parse_expr_pest(
                    tcx, def_id, &text,
                )))
            }
            spec::ArgKind::Ident => {
                let s = access_ident_recursive(expr)
                    .map(|(name, _)| name)
                    .unwrap_or_default();
                Some(PropertyArg::Ident(s))
            }
        }
    }

    /// Positional resolution over one of the spec's accepted forms.
    fn build_uniform(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        spec: &spec::PropertySpec,
        exprs: &[Expr],
    ) -> Self {
        let Some(form) = spec.forms.iter().find(|f| f.len() == exprs.len()) else {
            let expected: Vec<usize> = spec.forms.iter().map(|f| f.len()).collect();
            rap_error!(
                "Wrong args length for {:?} Tag! expected one of {expected:?}, got {}",
                spec.tag,
                exprs.len()
            );
            return Self::new_simple(PropertyKind::Unknown);
        };
        let mut args: Vec<PropertyArg<'tcx>> = Vec::with_capacity(exprs.len());
        for (expr, &arg_kind) in exprs.iter().zip(form.iter()) {
            let Some(arg) = Self::resolve_arg(tcx, def_id, spec.tag, arg_kind, expr) else {
                return Self::new_simple(PropertyKind::Unknown);
            };
            args.push(arg);
        }
        Self::new_atom(spec.kind, args)
    }

    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Self {
        match spec::find_spec(name) {
            Some(spec) => Self::parse_from_spec(tcx, def_id, spec, exprs),
            None => Self::new_simple(PropertyKind::Unknown),
        }
    }

    // ── Special-build constructors ───────────────────────────────

    fn build_size(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [ty_expr, const_expr] => {
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "Size") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                if let Some((ident, _)) = access_ident_recursive(const_expr) {
                    if ident == "sized" || ident == "unsized" {
                        return Self::new_with_args(
                            PropertyKind::Size,
                            vec![PropertyArg::Ty(ty), PropertyArg::Ident(ident)],
                        );
                    }
                }
                let c = super::resolve::expr_to_pest(tcx, def_id, const_expr);
                Self::new_with_args(
                    PropertyKind::Size,
                    vec![PropertyArg::Ty(ty), PropertyArg::Expr(c)],
                )
            }
            _ => {
                rap_error!(
                    "Wrong args length for Size Tag! expected 2, got {}",
                    exprs.len()
                );
                Self::new_simple(PropertyKind::Unknown)
            }
        }
    }

    fn build_allocated(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [target] => Self::new_with_args(
                PropertyKind::Allocated,
                vec![super::resolve::parse_target_arg(tcx, def_id, target)],
            ),
            [target_expr, ty_expr, len_expr] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, target_expr);
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "Allocated") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let length = super::resolve::expr_to_pest(tcx, def_id, len_expr);
                Self::new_with_args(
                    PropertyKind::Allocated,
                    vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                )
            }
            [target_expr, ty_expr, len_expr, allocator_expr] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, target_expr);
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "Allocated") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let length = super::resolve::expr_to_pest(tcx, def_id, len_expr);
                let allocator = access_ident_recursive(allocator_expr)
                    .map(|(name, _)| name)
                    .unwrap_or_else(|| "global".to_string());
                Self::new_with_args(
                    PropertyKind::Allocated,
                    vec![
                        target,
                        PropertyArg::Ty(ty),
                        PropertyArg::Expr(length),
                        PropertyArg::Ident(allocator),
                    ],
                )
            }
            _ => {
                rap_error!(
                    "Wrong args length for Allocated Tag! expected 1, 3 or 4, got {}",
                    exprs.len()
                );
                Self::new_simple(PropertyKind::Unknown)
            }
        }
    }

    fn build_inbound(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [expr] => {
                let expr = super::resolve::expr_to_pest(tcx, def_id, expr);
                if matches!(expr, ContractExpr::IndexAccess { .. }) {
                    Self::new_with_args(PropertyKind::InBound, vec![PropertyArg::Expr(expr)])
                } else {
                    Self::new_simple(PropertyKind::Unknown)
                }
            }
            [_target, ty_expr, len_expr] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, &exprs[0]);
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "InBound") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let length = super::resolve::expr_to_pest(tcx, def_id, len_expr);
                Self::new_with_args(
                    PropertyKind::InBound,
                    vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                )
            }
            [target, index_expr] => {
                let slice = super::resolve::expr_to_pest(tcx, def_id, target);
                let index = super::resolve::expr_to_pest(tcx, def_id, index_expr);
                if matches!(slice, ContractExpr::Unknown)
                    || matches!(index, ContractExpr::Unknown)
                {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                // Auto-detect array index for for_each
                let for_each = super::place::detect_array_for_each(tcx, def_id, index_expr);
                let mut prop = Self::new_atom(
                    PropertyKind::InBound,
                    vec![PropertyArg::Expr(ContractExpr::IndexAccess {
                        slice: Box::new(slice),
                        index: Box::new(index),
                    })],
                );
                prop.set_for_each(for_each);
                prop
            }
            _ => {
                Self::check_arg_length(exprs.len(), 3, "InBound");
                Self::new_simple(PropertyKind::Unknown)
            }
        }
    }

    fn build_nonoverlap(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [indices] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, indices);
                Self::new_with_args(PropertyKind::NonOverlap, vec![target])
            }
            [a, b, ty_expr, count_expr] => {
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "NonOverlap")
                else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let left = super::resolve::parse_target_arg(tcx, def_id, a);
                let right = super::resolve::parse_target_arg(tcx, def_id, b);
                let count = super::resolve::expr_to_pest(tcx, def_id, count_expr);
                Self::new_with_args(
                    PropertyKind::NonOverlap,
                    vec![left, right, PropertyArg::Ty(ty), PropertyArg::Expr(count)],
                )
            }
            _ => {
                rap_error!(
                    "Wrong args length for NonOverlap Tag! expected 1 or 4, got {}",
                    exprs.len()
                );
                Self::new_simple(PropertyKind::Unknown)
            }
        }
    }

    fn build_validnum(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        let predicates = super::resolve::parse_valid_num(tcx, def_id, exprs);
        if predicates.is_empty() {
            Self::new_simple(PropertyKind::Unknown)
        } else {
            Self::new_with_args(
                PropertyKind::ValidNum,
                vec![PropertyArg::Predicates(predicates)],
            )
        }
    }

    fn build_targets(
        spec: &spec::PropertySpec,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Self {
        Self::new_with_targets(spec.kind, tcx, def_id, exprs)
    }

    fn build_pinned(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [ptr_expr, lifetime_expr] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, ptr_expr);
                let Some((lifetime, _)) = access_ident_recursive(lifetime_expr) else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_with_args(
                    PropertyKind::Pinned,
                    vec![target, PropertyArg::Ident(lifetime)],
                )
            }
            _ => {
                rap_error!(
                    "Wrong args length for Pinned Tag! expected 2, got {}",
                    exprs.len()
                );
                Self::new_simple(PropertyKind::Unknown)
            }
        }
    }

    fn build_split_transmute(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        if !Self::check_arg_length(exprs.len(), 2, "SplitTransmute") {
            return Self::new_simple(PropertyKind::Unknown);
        }
        let src_elem = super::resolve::unwrap_array_expr(tcx, def_id, &exprs[0]);
        let dst_elem = super::resolve::unwrap_array_expr(tcx, def_id, &exprs[1]);
        let (Some(src_elem), Some(dst_elem)) = (src_elem, dst_elem) else {
            return Self::new_simple(PropertyKind::Unknown);
        };
        Self::new_with_args(
            PropertyKind::SplitTransmute,
            vec![PropertyArg::Ty(src_elem), PropertyArg::Ty(dst_elem)],
        )
    }

    fn new_simple(kind: PropertyKind) -> Self {
        Self::new_atom(kind, Vec::new())
    }

    /// Parse one annotation entry into the properties it denotes.
    ///
    /// Plain entries (`Align(p, T)`, `Owning(p)`, ...) yield one property.
    /// The `any(...)` combinator may expand to several: see [`Self::parse_any`].
    pub fn parse_list(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Vec<Self> {
        // User-defined / compound `def` macro expansion takes precedence, so
        // `#[rapx::requires(MyTag(...))]` can reference DSL-defined contracts.
        if let Some(props) = super::def::expand_def(tcx, def_id, name, exprs) {
            return props;
        }
        let mut props = if name == "any" {
            Self::parse_any(tcx, def_id, exprs)
        } else {
            vec![Self::new(tcx, def_id, name, exprs)]
        };
        for prop in &mut props {
            if let Property::Atom(atom) = prop {
                if atom.for_each.is_none() {
                    for arg in &mut atom.args {
                        atom.for_each = super::place::strip_for_each(arg);
                        if atom.for_each.is_some() {
                            break;
                        }
                    }
                }
            }
        }
        props
    }

    /// Parse the disjunctive combinator `any(D1, D2, ...)` written in DNF:
    /// `any` means logical OR between disjuncts, and commas inside a
    /// parenthesised disjunct mean logical AND:
    ///
    /// ```text
    /// any(Null(p), (P1(p, ...), P2(p, ...), ...))
    /// ```
    ///
    /// A disjunct is either a single property application `P(...)` or a
    /// parenthesised conjunction `(P1(...), ..., Pn(...))`.  Two patterns are
    /// supported:
    ///
    /// 1. **Null guard**: exactly two disjuncts, one being `Null(p)` alone,
    ///    the other a conjunction of properties over the same place `p`.  The
    ///    disjunction expands to an `Or` whose disjuncts are `Null(p)` and an
    ///    `And` of the conjuncts.
    ///
    /// 2. **General disjunction**: each disjunct is standalone or a
    ///    conjunction, e.g., `any(Trait(T, Copy), Trait(T, TrivialClone))`.
    ///    Produces a single `Property::Or` whose `disjuncts` are atoms or
    ///    `And` nodes.
    fn parse_any(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Vec<Self> {
        if !Self::check_arg_length(exprs.len(), 2, "any") {
            return vec![Self::new_simple(PropertyKind::Unknown)];
        }

        let (Some(first), Some(second)) = (
            Self::disjunct_parts(&exprs[0]),
            Self::disjunct_parts(&exprs[1]),
        ) else {
            rap_error!("any(...) disjuncts must be property applications or (P1, P2, ...) groups");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        };

        // --- null-guard pattern ---
        let is_null_guard =
            |disjunct: &[(String, Vec<Expr>)]| disjunct.len() == 1 && disjunct[0].0 == "Null";
        if is_null_guard(&first) && !is_null_guard(&second) {
            return Self::build_null_guard(tcx, def_id, &first, &second);
        }
        if is_null_guard(&second) && !is_null_guard(&first) {
            return Self::build_null_guard(tcx, def_id, &second, &first);
        }

        // --- general disjunction: build a single Or property ---
        let all_standalone = [&first, &second].iter().all(|d| d.len() == 1);
        if all_standalone {
            let mut disjuncts: Vec<Self> = Vec::new();
            for parts in [first, second] {
                let mut conjuncts: Vec<Self> = Vec::new();
                for (name, args) in parts {
                    conjuncts.extend(Self::parse_list(tcx, def_id, &name, &args));
                }
                disjuncts.push(Self::conjunction(conjuncts));
            }
            return vec![Self::new_or(disjuncts)];
        }

        rap_error!(
            "any(...) currently supports either a Null(p) guard pattern or \
             standalone property applications"
        );
        vec![Self::new_simple(PropertyKind::Unknown)]
    }

    /// Build the null-guard disjunction: `Null(p) OR (P1 & P2 & ...)`.
    ///
    /// Produces an `Or` whose disjuncts are `Null(p)` and an `And` of the
    /// expanded conjuncts.
    fn build_null_guard(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        guard: &[(String, Vec<Expr>)],
        conjuncts: &[(String, Vec<Expr>)],
    ) -> Vec<Self> {
        let guard_args = &guard[0].1;
        if guard_args.len() != 1 {
            rap_error!("Null(...) guard inside any(...) takes exactly one place");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        }
        let Some(guard_place) = super::place::parse_contract_place(tcx, def_id, &guard_args[0]) else {
            rap_error!("cannot resolve the place guarded by Null(...) inside any(...)");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        };

        let null_atom = Self::new_atom(
            PropertyKind::Null,
            vec![PropertyArg::Expr(ContractExpr::Place(guard_place.clone()))],
        );

        let mut expanded: Vec<Self> = Vec::new();
        for (inner_name, inner_args) in conjuncts {
            // Use `parse_list` so a compound `def` conjunct (e.g. `ValidPtr`)
            // expands to its primitive components, each over the guarded place.
            for property in Self::parse_list(tcx, def_id, inner_name, inner_args) {
                if !Self::conjuncts_guard_place(&property, &guard_place) {
                    rap_error!(
                        "any(Null(p), ...) requires every conjunct ({inner_name}) to \
                         constrain the guarded place"
                    );
                    return vec![Self::new_simple(PropertyKind::Unknown)];
                }
                expanded.push(property);
            }
        }

        vec![Self::new_or(vec![null_atom, Self::conjunction(expanded)])]
    }

    /// Returns true when every place-bearing atom of `property` constrains the
    /// guarded place.  Used to reject a malformed `any(Null(p), ...)` whose
    /// conjunct targets a different place than the guard.
    fn conjuncts_guard_place(
        property: &Property<'tcx>,
        guard_place: &ContractPlace<'tcx>,
    ) -> bool {
        match property {
            Property::Or(or) => or
                .disjuncts
                .iter()
                .all(|sub| Self::conjuncts_guard_place(sub, guard_place)),
            Property::And(and) => and
                .conjuncts
                .iter()
                .all(|sub| Self::conjuncts_guard_place(sub, guard_place)),
            Property::Atom(atom) => {
                if let Some(PropertyArg::Expr(ContractExpr::Place(place))) = atom.args.first() {
                    crate::verify::def_use::PlaceKey::from_contract_place(place)
                        == crate::verify::def_use::PlaceKey::from_contract_place(guard_place)
                } else {
                    true
                }
            }
        }
    }

    /// Split one disjunct into its conjunct calls: a `(P1, P2, ...)` tuple, a
    /// parenthesised single property `(P)`, or a bare property application.
    fn disjunct_parts(expr: &Expr) -> Option<Vec<(String, Vec<Expr>)>> {
        match expr {
            Expr::Tuple(tuple) => tuple.elems.iter().map(Self::call_parts).collect(),
            Expr::Paren(paren) => Self::call_parts(&paren.expr).map(|parts| vec![parts]),
            _ => Self::call_parts(expr).map(|parts| vec![parts]),
        }
    }

    /// Split a `Name(arg, ...)` call expression into its name and arguments.
    fn call_parts(expr: &Expr) -> Option<(String, Vec<Expr>)> {
        let Expr::Call(call) = expr else {
            return None;
        };
        let Expr::Path(path) = call.func.as_ref() else {
            return None;
        };
        let name = path.path.get_ident()?.to_string();
        Some((name, call.args.iter().cloned().collect()))
    }

    fn new_with_args(kind: PropertyKind, args: Vec<PropertyArg<'tcx>>) -> Self {
        Self::new_atom(kind, args)
    }

    fn new_with_targets(
        kind: PropertyKind,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Self {
        let (args, for_each) = Self::parse_target_args_with_for_each(tcx, def_id, exprs);
        let mut prop = Self::new_atom(kind, args);
        prop.set_for_each(for_each);
        prop
    }

    fn parse_target_args_with_for_each(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> (Vec<PropertyArg<'tcx>>, Option<ContractPlace<'tcx>>) {
        let raw_args: Vec<_> = exprs
            .iter()
            .map(|expr| super::resolve::parse_target_arg(tcx, def_id, expr))
            .collect();
        let mut for_each = None;
        let mut clean_args = Vec::with_capacity(raw_args.len());
        for arg in raw_args {
            let mut clean = arg;
            if for_each.is_none() {
                if let Some(container) = super::place::strip_for_each(&mut clean) {
                    for_each = Some(container);
                }
            }
            clean_args.push(clean);
        }
        // Auto-detect array arguments: if no explicit .iter() was used
        // but an argument is an array type [T; N], automatically set
        // for_each so the property is checked per-element.
        if for_each.is_none() {
            let fn_sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
            for (i, arg_ty) in fn_sig.inputs().iter().enumerate() {
                if let rustc_middle::ty::TyKind::Array(..) = arg_ty.kind() {
                    for_each = Some(crate::verify::contract::ContractPlace {
                        base: PlaceBase::Arg(i),
                        projections: vec![],
                    });
                    break;
                }
            }
        }
        (clean_args, for_each)
    }

    fn check_arg_length(expr_len: usize, required_len: usize, sp: &str) -> bool {
        if expr_len != required_len {
            rap_error!(
                "Wrong args length for {:?} Tag! expected {required_len}, got {expr_len}",
                sp
            );
            return false;
        }
        true
    }
}

