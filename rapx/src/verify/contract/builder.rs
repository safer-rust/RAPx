//! Assemble a safety tag into a [`Property`] via the declarative spec table.
//!
//! `Property::new` looks up `spec::SPECS`, dispatches on the tag's `BuildKind`,
//! and resolves arguments positionally. `Property::parse_list` is the shared
//! entry point for all front-ends, including the `any(...)` combinator.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use syn::Expr;

use crate::helpers::name::access_ident_recursive;

use super::spec;
use super::types::*;

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
            spec::BuildKind::NotType => Self::build_not_type(tcx, def_id, exprs),
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
            spec::ArgKind::Expr => Some(PropertyArg::Expr(super::resolve::expr_to_pest(
                tcx, def_id, expr,
            ))),
            spec::ArgKind::Ident => {
                let s = access_ident_recursive(expr).map(|(name, _)| name)?;
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

    pub(crate) fn new(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Self {
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
                        return Self::new_atom(
                            PropertyKind::Size,
                            vec![PropertyArg::Ty(ty), PropertyArg::Ident(ident)],
                        );
                    }
                }
                let c = super::resolve::expr_to_pest(tcx, def_id, const_expr);
                Self::new_atom(
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
            [target] => Self::new_atom(
                PropertyKind::Allocated,
                vec![super::resolve::parse_target_arg(tcx, def_id, target)],
            ),
            [target_expr, ty_expr, len_expr] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, target_expr);
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "Allocated") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let length = super::resolve::expr_to_pest(tcx, def_id, len_expr);
                Self::new_atom(
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
                Self::new_atom(
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
                    Self::new_atom(PropertyKind::InBound, vec![PropertyArg::Expr(expr)])
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
                Self::new_atom(
                    PropertyKind::InBound,
                    vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                )
            }
            [target, index_expr] => {
                let slice = super::resolve::expr_to_pest(tcx, def_id, target);
                let index = super::resolve::expr_to_pest(tcx, def_id, index_expr);
                if matches!(slice, ContractExpr::Unknown) || matches!(index, ContractExpr::Unknown)
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
                rap_error!(
                    "Wrong args length for InBound Tag! expected 1, 2 or 3, got {}",
                    exprs.len()
                );
                Self::new_simple(PropertyKind::Unknown)
            }
        }
    }

    fn build_nonoverlap(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [indices] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, indices);
                Self::new_atom(PropertyKind::NonOverlap, vec![target])
            }
            [a, b, ty_expr, count_expr] => {
                let Some(ty) = super::resolve::parse_type(tcx, def_id, ty_expr, "NonOverlap")
                else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let left = super::resolve::parse_target_arg(tcx, def_id, a);
                let right = super::resolve::parse_target_arg(tcx, def_id, b);
                let count = super::resolve::expr_to_pest(tcx, def_id, count_expr);
                Self::new_atom(
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
            Self::new_atom(
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
        let args = exprs
            .iter()
            .map(|expr| super::resolve::parse_target_arg(tcx, def_id, expr))
            .collect();
        Self::new_atom(spec.kind, args)
    }

    fn build_pinned(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        match exprs {
            [ptr_expr, lifetime_expr] => {
                let target = super::resolve::parse_target_arg(tcx, def_id, ptr_expr);
                let Some((lifetime, _)) = access_ident_recursive(lifetime_expr) else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_atom(
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
        Self::new_atom(
            PropertyKind::SplitTransmute,
            vec![PropertyArg::Ty(src_elem), PropertyArg::Ty(dst_elem)],
        )
    }

    fn build_not_type(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Self {
        if exprs.len() < 2 {
            rap_error!(
                "Wrong args length for NotType Tag! expected at least 2 (ty, ident...), got {}",
                exprs.len()
            );
            return Self::new_simple(PropertyKind::Unknown);
        }
        let Some(ty) = super::resolve::parse_type(tcx, def_id, &exprs[0], "NotType") else {
            return Self::new_simple(PropertyKind::Unknown);
        };
        let mut args = vec![PropertyArg::Ty(ty)];
        for expr in &exprs[1..] {
            let Some((name, _)) = access_ident_recursive(expr) else {
                return Self::new_simple(PropertyKind::Unknown);
            };
            args.push(PropertyArg::Ident(name));
        }
        Self::new_atom(PropertyKind::NotType, args)
    }

    fn new_simple(kind: PropertyKind) -> Self {
        Self::new_atom(kind, Vec::new())
    }

    /// Parse one annotation entry into the properties it denotes.
    ///
    /// Plain entries (`Align(p, T)`, `Owning(p)`, ...) yield one property.
    /// The `any(...)` combinator may expand to several: see [`Self::parse_any`].
    pub(crate) fn parse_list(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        name: &str,
        exprs: &[Expr],
    ) -> Vec<Self> {
        // User-defined / compound property macro expansion takes precedence, so
        // `#[rapx::requires(MyTag(...))]` can reference DSL-defined contracts.
        if let Some(props) = super::compound::expand_compound(tcx, def_id, name, exprs) {
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
    /// any(Trait(T, Copy), Trait(T, TrivialClone), ...)
    /// ```
    ///
    /// A disjunct is either a single property application `P(...)` or a
    /// parenthesised conjunction `(P1(...), ..., Pn(...))`.  Any number (≥ 2)
    /// of disjuncts is accepted; each is expanded into its constituent
    /// properties, producing a single `Property::Or` whose disjuncts are atoms
    /// or `And` nodes.
    fn parse_any(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Vec<Self> {
        if exprs.len() < 2 {
            rap_error!(
                "any(...) requires at least 2 disjuncts, got {}",
                exprs.len()
            );
            return vec![Self::new_simple(PropertyKind::Unknown)];
        }

        let mut disjuncts: Vec<Vec<(String, Vec<Expr>)>> = Vec::with_capacity(exprs.len());
        for expr in exprs {
            let Some(parts) = Self::disjunct_parts(expr) else {
                rap_error!(
                    "any(...) disjuncts must be property applications or (P1, P2, ...) groups"
                );
                return vec![Self::new_simple(PropertyKind::Unknown)];
            };
            disjuncts.push(parts);
        }

        let mut or_disjuncts: Vec<Self> = Vec::with_capacity(disjuncts.len());
        for parts in disjuncts {
            let mut conjuncts: Vec<Self> = Vec::new();
            for (name, args) in parts {
                conjuncts.extend(Self::parse_list(tcx, def_id, &name, &args));
            }
            or_disjuncts.push(Self::conjunction(conjuncts));
        }
        vec![Self::new_or(or_disjuncts)]
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
