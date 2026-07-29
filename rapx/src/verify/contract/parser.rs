use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericParamDefKind, Ty, TyCtxt, TyKind};
use safety_parser::syn::{Expr, GenericArgument, Lit, PathArguments, Type};

use crate::helpers::fn_info::{FnKind, get_type, parse_expr_into_number};
use crate::helpers::name::{
    access_ident_recursive, get_struct_self_ty, match_ty_with_ident, parse_signature,
};

use super::types::*;
use super::spec;

impl<'tcx> Property<'tcx> {
    /// Parse a property using the fixed-arity declaration table.
    fn parse_from_spec(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        spec: &spec::PropertySpec,
        exprs: &[Expr],
    ) -> Self {
        if !Self::check_arg_length(exprs.len(), spec.args.len(), spec.tag) {
            return Self::new_simple(PropertyKind::Unknown);
        }
        let args: Vec<PropertyArg<'tcx>> = exprs
            .iter()
            .zip(spec.args.iter())
            .map(|(expr, &arg_kind)| match arg_kind {
                spec::ArgKind::Target => Self::parse_target_arg(tcx, def_id, expr),
                spec::ArgKind::Ty => {
                    let ty = Self::parse_type(tcx, def_id, expr, spec.tag)
                        .unwrap_or_else(|| tcx.types.never);
                    PropertyArg::Ty(ty)
                }
                spec::ArgKind::Expr => {
                    PropertyArg::Expr(Self::parse_contract_expr(tcx, def_id, expr, spec.tag))
                }
                spec::ArgKind::Ident => {
                    let s = access_ident_recursive(expr)
                        .map(|(name, _)| name)
                        .unwrap_or_default();
                    PropertyArg::Ident(s)
                }
            })
            .collect();
        Self {
            kind: spec.kind,
            args,
            contract_kind: spec.contract_kind,
            null_guard: None,
            or_alternatives: Vec::new(),
            for_each: None,
        }
    }

    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Self {
        if let Some(spec) = spec::find_spec(name) {
            return Self::parse_from_spec(tcx, def_id, spec, exprs);
        }
        match name {
            "Size" | "NonSize" => match exprs {
                [ty_expr, const_expr] => {
                    let mut args = Vec::new();
                    if let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "Size") {
                        args.push(PropertyArg::Ty(ty));
                    }
                    if let Some((ident, _)) = access_ident_recursive(const_expr) {
                        if ident == "sized" || ident == "unsized" {
                            args.push(PropertyArg::Ident(ident));
                            return Self::new_with_args(PropertyKind::Size, args);
                        }
                    }
                    let c = Self::parse_contract_expr(tcx, def_id, const_expr, "Size");
                    args.push(PropertyArg::Expr(c));
                    Self::new_with_args(PropertyKind::Size, args)
                }
                _ => {
                    rap_error!(
                        "Wrong args length for Size Tag! expected 2, got {}",
                        exprs.len()
                    );
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "Allocated" => match exprs {
                [target] => Self::new_with_args(
                    PropertyKind::Allocated,
                    vec![Self::parse_target_arg(tcx, def_id, target)],
                ),
                [target_expr, ty_expr, len_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, target_expr);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "Allocated") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "Allocated");
                    Self::new_with_args(
                        PropertyKind::Allocated,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                [target_expr, ty_expr, len_expr, allocator_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, target_expr);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "Allocated") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "Allocated");
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
                        "Wrong args length for Allocated Tag! expected 3 or 4, got {}",
                        exprs.len()
                    );
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "InBound" | "InBounded" => match exprs {
                [expr] => {
                    let expr = Self::parse_contract_expr(tcx, def_id, expr, "InBound");
                    if matches!(expr, ContractExpr::IndexAccess { .. }) {
                        Self::new_with_args(PropertyKind::InBound, vec![PropertyArg::Expr(expr)])
                    } else {
                        Self::new_simple(PropertyKind::Unknown)
                    }
                }
                [_target, ty_expr, len_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "InBound") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "InBound");
                    Self::new_with_args(
                        PropertyKind::InBound,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                [target, index_expr] => {
                    let slice = Self::parse_contract_expr(tcx, def_id, target, "InBound");
                    let index = Self::parse_contract_expr(tcx, def_id, index_expr, "InBound");
                    if matches!(slice, ContractExpr::Unknown)
                        || matches!(index, ContractExpr::Unknown)
                    {
                        return Self::new_simple(PropertyKind::Unknown);
                    }
                    Self::new_with_args(
                        PropertyKind::InBound,
                        vec![PropertyArg::Expr(ContractExpr::IndexAccess {
                            slice: Box::new(slice),
                            index: Box::new(index),
                        })],
                    )
                }
                _ => {
                    Self::check_arg_length(exprs.len(), 3, "InBound");
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "NonOverlap" => match exprs {
                [indices] => {
                    let target = Self::parse_target_arg(tcx, def_id, indices);
                    Self::new_with_args(PropertyKind::NonOverlap, vec![target])
                }
                [a, b, ty_expr, count_expr] => {
                    let left = Self::parse_target_arg(tcx, def_id, a);
                    let right = Self::parse_target_arg(tcx, def_id, b);
                    let count = Self::parse_contract_expr(tcx, def_id, count_expr, "NonOverlap");
                    let mut args = vec![left, right];
                    if let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "NonOverlap") {
                        args.push(PropertyArg::Ty(ty));
                    }
                    args.push(PropertyArg::Expr(count));
                    Self::new_with_args(PropertyKind::NonOverlap, args)
                }
                _ => {
                    rap_error!(
                        "Wrong args length for NonOverlap Tag! expected 4, got {}",
                        exprs.len()
                    );
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "ValidNum" => {
                let predicates = Self::parse_valid_num(tcx, def_id, exprs);
                if predicates.is_empty() {
                    Self::new_simple(PropertyKind::Unknown)
                } else {
                    Self::new_with_args(
                        PropertyKind::ValidNum,
                        vec![PropertyArg::Predicates(predicates)],
                    )
                }
            }
            "Alias" => {
                let mut prop = Self::new_with_targets(PropertyKind::Alias, tcx, def_id, exprs);
                prop.contract_kind = ContractKind::Hazard;
                prop
            }
            "Alive" => Self::new_with_targets(PropertyKind::Alive, tcx, def_id, exprs),
            "Pinned" => match exprs {
                [ptr_expr, lifetime_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, ptr_expr);
                    let lifetime = access_ident_recursive(lifetime_expr)
                        .map(|(name, _)| name)
                        .unwrap_or_default();
                    let mut args = vec![target];
                    if !lifetime.is_empty() {
                        args.push(PropertyArg::Ident(lifetime));
                    }
                    Self::new_with_args(PropertyKind::Pinned, args)
                }
                _ => {
                    rap_error!(
                        "Wrong args length for Pinned Tag! expected 2, got {}",
                        exprs.len()
                    );
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "SplitTransmute" => {
                if !Self::check_arg_length(exprs.len(), 2, "SplitTransmute") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let src_elem = unwrap_array_expr(tcx, def_id, &exprs[0]);
                let dst_elem = unwrap_array_expr(tcx, def_id, &exprs[1]);
                let (Some(src_elem), Some(dst_elem)) = (src_elem, dst_elem) else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_with_args(
                    PropertyKind::SplitTransmute,
                    vec![PropertyArg::Ty(src_elem), PropertyArg::Ty(dst_elem)],
                )
            }
            "TobeSpecified" => {
                // Placeholder for safety conditions not yet modeled as RAPx contracts.
                // Accepts any args without error; evaluates as a no-op at verification time.
                Self::new_simple(PropertyKind::Unknown)
            }
            _ => Self::new_simple(PropertyKind::Unknown),
        }
    }

    pub fn display_for_report(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        let kind_str = format!("{:?}", self.kind);

        if matches!(self.kind, PropertyKind::InBound)
            && matches!(
                self.args.first(),
                Some(PropertyArg::Expr(ContractExpr::IndexAccess { .. }))
            )
        {
            if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
                self.args.first()
            {
                let slice_str = display_expr_user_friendly(slice, tcx, struct_def_id, fn_def_id);
                let index_str = display_expr_user_friendly(index, tcx, struct_def_id, fn_def_id);
                return format!("{}({}, {})", kind_str, slice_str, index_str);
            }
        }

        if matches!(self.kind, PropertyKind::ValidNum)
            && let Some(PropertyArg::Predicates(preds)) = self.args.first()
        {
            let inner: Vec<String> = preds
                .iter()
                .map(|pred| pred.display_user_friendly(tcx, struct_def_id, fn_def_id))
                .collect();
            if inner.is_empty() {
                return format!("{}", kind_str);
            }
            return format!("{}({})", kind_str, inner.join(", "));
        }

        let args: Vec<String> = self
            .args
            .iter()
            .map(|arg| arg.display_for_report(tcx, struct_def_id, fn_def_id))
            .collect();
        if args.is_empty() {
            kind_str
        } else {
            format!("{}({})", kind_str, args.join(", "))
        }
    }

    fn new_simple(kind: PropertyKind) -> Self {
        Self {
            kind,
            args: Vec::new(),
            contract_kind: ContractKind::Precond,
            null_guard: None,
            or_alternatives: Vec::new(),
            for_each: None,
        }
    }

    /// Parse one annotation entry into the properties it denotes.
    ///
    /// Plain entries (`Align(p, T)`, `Owning(p)`, ...) yield one property.
    /// The `any(...)` combinator may expand to several: see [`Self::parse_any`].
    pub fn parse_list(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Vec<Self> {
        let mut props = if name == "any" {
            Self::parse_any(tcx, def_id, exprs)
        } else {
            vec![Self::new(tcx, def_id, name, exprs)]
        };
        for prop in &mut props {
            if prop.for_each.is_none() {
                for arg in &mut prop.args {
                    prop.for_each = strip_iter_elements(arg);
                    if prop.for_each.is_some() {
                        break;
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
    ///    disjunction expands to the conjunct properties, each holding
    ///    whenever `p` is non-null and vacuously for a null `p`.
    ///
    /// 2. **General disjunction**: each disjunct is standalone or a
    ///    conjunction, e.g., `any(Trait(T, Copy), Trait(T, TrivialClone))`.
    ///    Produces a single `PropertyKind::Or` whose `or_alternatives`
    ///    encode the DNF structure: each inner `Vec` is one AND-group.
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
            let mut groups: Vec<Vec<Box<Self>>> = Vec::new();
            for parts in [first, second] {
                let mut group: Vec<Box<Self>> = Vec::new();
                for (name, args) in parts {
                    group.push(Box::new(Self::new(tcx, def_id, &name, &args)));
                }
                groups.push(group);
            }
            let mut or_prop = Self::new_simple(PropertyKind::Or);
            or_prop.or_alternatives = groups;
            return vec![or_prop];
        }

        rap_error!(
            "any(...) currently supports either a Null(p) guard pattern or \
             standalone property applications"
        );
        vec![Self::new_simple(PropertyKind::Unknown)]
    }

    /// Build the null-guard expansion: `Null(p) OR (P1 & P2 & ...)`.
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
        let Some(guard_place) = Self::parse_contract_place(tcx, def_id, &guard_args[0]) else {
            rap_error!("cannot resolve the place guarded by Null(...) inside any(...)");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        };
        let guard_key = crate::verify::def_use::PlaceKey::from_contract_place(&guard_place);

        let mut properties = Vec::new();
        for (inner_name, inner_args) in conjuncts {
            let mut property = Self::new(tcx, def_id, inner_name, inner_args);
            let inner_place = property.args.first().and_then(|arg| match arg {
                PropertyArg::Place(place) => Some(place),
                PropertyArg::Expr(ContractExpr::Place(place)) => Some(place),
                _ => None,
            });
            let places_match = inner_place.is_some_and(|place| {
                crate::verify::def_use::PlaceKey::from_contract_place(place) == guard_key
            });
            if !places_match {
                rap_error!(
                    "any(Null(p), ...) requires every conjunct ({inner_name}) to \
                     constrain the guarded place"
                );
                return vec![Self::new_simple(PropertyKind::Unknown)];
            }
            property.null_guard = Some(guard_key.clone());
            properties.push(property);
        }
        properties
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
        Self {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            null_guard: None,
            or_alternatives: Vec::new(),
            for_each: None,
        }
    }

    fn new_with_targets(
        kind: PropertyKind,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Self {
        let (args, for_each) = Self::parse_target_args_with_for_each(tcx, def_id, exprs);
        Self {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            null_guard: None,
            or_alternatives: Vec::new(),
            for_each,
        }
    }

    fn parse_target_args_with_for_each(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> (Vec<PropertyArg<'tcx>>, Option<ContractPlace<'tcx>>) {
        let raw_args: Vec<_> = exprs
            .iter()
            .map(|expr| Self::parse_target_arg(tcx, def_id, expr))
            .collect();
        let mut for_each = None;
        let mut clean_args = Vec::with_capacity(raw_args.len());
        for arg in raw_args {
            let mut clean = arg;
            if for_each.is_none() {
                if let Some(container) = strip_iter_elements(&mut clean) {
                    for_each = Some(container);
                }
            }
            clean_args.push(clean);
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

    fn parse_type(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr, sp: &str) -> Option<Ty<'tcx>> {
        let ty_ident_full = access_ident_recursive(expr);
        if ty_ident_full.is_none() {
            rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
            return None;
        }
        let ty_ident = ty_ident_full.unwrap().0;
        let ty = match_ty_with_ident(tcx, def_id, ty_ident);
        if ty.is_none() {
            rap_debug!("Cannot get type in {:?} Tag!", sp);
        }
        ty
    }

    fn parse_target_arg(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> PropertyArg<'tcx> {
        // For simple identifiers that aren't local variables (e.g., lifetime param 'a
        // parsed as ident `a`), store as Ident rather than Expr which would become Unknown.
        if let Expr::Path(expr_path) = expr {
            if let Some(ident) = expr_path.path.get_ident() {
                let s = ident.to_string();
                if s != "return"
                    && !s.starts_with("Arg_")
                    && parse_expr_into_local_and_ty(tcx, def_id, expr).is_none()
                {
                    return PropertyArg::Ident(s);
                }
            }
        }
        Self::parse_contract_place(tcx, def_id, expr)
            .map(PropertyArg::Place)
            .unwrap_or_else(|| {
                PropertyArg::Expr(Self::parse_contract_expr(tcx, def_id, expr, "target"))
            })
    }

    fn parse_contract_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
        sp: &str,
    ) -> ContractExpr<'tcx> {
        match expr {
            Expr::Paren(paren) => Self::parse_contract_expr(tcx, def_id, &paren.expr, sp),
            Expr::Group(group) => Self::parse_contract_expr(tcx, def_id, &group.expr, sp),
            Expr::Lit(expr_lit) => match &expr_lit.lit {
                Lit::Int(lit_int) => lit_int
                    .base10_parse::<u128>()
                    .map(ContractExpr::Const)
                    .unwrap_or(ContractExpr::Unknown),
                _ => ContractExpr::Unknown,
            },
            Expr::Call(expr_call) => {
                if let Some(expr) = Self::parse_index_access_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                if let Some(expr) = Self::parse_len_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                if let Some(expr) = Self::parse_layout_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                if let Some(expr) = Self::parse_builtin_fn_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                ContractExpr::Unknown
            }
            // Treat `x.len` (field-access sugar) as the slice length `len(x)`.
            Expr::Field(expr_field) if matches!(&expr_field.member, safety_parser::syn::Member::Named(ident) if ident == "len") => {
                ContractExpr::Len(Box::new(Self::parse_contract_expr(
                    tcx,
                    def_id,
                    &expr_field.base,
                    sp,
                )))
            }
            // Treat `self.len()` (method-call sugar) as the slice length `len(self)`.
            Expr::MethodCall(expr_method)
                if expr_method.method == "len" && expr_method.args.is_empty() =>
            {
                ContractExpr::Len(Box::new(Self::parse_contract_expr(
                    tcx,
                    def_id,
                    &expr_method.receiver,
                    sp,
                )))
            }
            Expr::Unary(expr_unary) => {
                let Some(op) = NumericUnaryOp::from_syn(&expr_unary.op) else {
                    return ContractExpr::Unknown;
                };
                ContractExpr::Unary {
                    op,
                    expr: Box::new(Self::parse_contract_expr(tcx, def_id, &expr_unary.expr, sp)),
                }
            }
            Expr::Binary(expr_binary) => {
                let Some(op) = NumericOp::from_syn(&expr_binary.op) else {
                    return ContractExpr::Unknown;
                };
                ContractExpr::Binary {
                    op,
                    lhs: Box::new(Self::parse_contract_expr(
                        tcx,
                        def_id,
                        &expr_binary.left,
                        sp,
                    )),
                    rhs: Box::new(Self::parse_contract_expr(
                        tcx,
                        def_id,
                        &expr_binary.right,
                        sp,
                    )),
                }
            }
            Expr::Path(expr_path) => Self::parse_path_constant(tcx, def_id, expr_path)
                .unwrap_or_else(|| Self::fallback_contract_expr(tcx, def_id, expr, sp)),
            _ => Self::fallback_contract_expr(tcx, def_id, expr, sp),
        }
    }

    fn fallback_contract_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
        sp: &str,
    ) -> ContractExpr<'tcx> {
        if let Some(place) = Self::parse_contract_place(tcx, def_id, expr) {
            ContractExpr::Place(place)
        } else if let Some(expr) = Self::parse_const_param(tcx, def_id, expr) {
            expr
        } else if let Some(value) = Self::parse_builtin_const(tcx, expr) {
            ContractExpr::Const(value)
        } else if let Some(value) = parse_expr_into_number(expr) {
            ContractExpr::new_value(value)
        } else {
            rap_debug!(
                "Numeric expression in {:?} could not be resolved: {:?}",
                sp,
                expr
            );
            ContractExpr::Unknown
        }
    }

    fn parse_path_constant(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_path: &safety_parser::syn::ExprPath,
    ) -> Option<ContractExpr<'tcx>> {
        let segments = &expr_path.path.segments;
        if segments.len() != 2 {
            return None;
        }
        let type_name = segments[0].ident.to_string();
        let const_name = segments[1].ident.to_string();
        if !matches!(const_name.as_str(), "MIN" | "MAX") {
            return None;
        }
        let ty = Self::resolve_type_name(tcx, def_id, &type_name)?;
        let (min, max) = Self::int_type_min_max(tcx, ty)?;
        let value = if const_name == "MIN" { min } else { max };
        Some(ContractExpr::Const(value))
    }

    fn resolve_type_name(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str) -> Option<Ty<'tcx>> {
        if name == "Self" {
            let sig = tcx.fn_sig(def_id).skip_binder();
            return sig.inputs().skip_binder().first().copied();
        }
        match_ty_with_ident(tcx, def_id, name.to_string())
    }

    fn int_type_min_max(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u128, u128)> {
        use rustc_middle::ty::IntTy;
        use rustc_middle::ty::UintTy;
        let bits: u32 = match ty.kind() {
            TyKind::Uint(ut) => match ut {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => tcx.data_layout.pointer_size().bits() as u32,
            },
            TyKind::Int(it) => match it {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => tcx.data_layout.pointer_size().bits() as u32,
            },
            _ => return None,
        };
        if bits == 0 {
            return None;
        }
        match ty.kind() {
            TyKind::Uint(_) => {
                let max = if bits == 128 {
                    u128::MAX
                } else {
                    (1u128 << bits) - 1
                };
                Some((0, max))
            }
            TyKind::Int(_) => {
                let max = (1u128 << (bits - 1)) - 1;
                let min = max + 1;
                Some((min, max))
            }
            _ => None,
        }
    }

    fn parse_index_access_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let name = func_path.path.segments.last()?.ident.to_string();
        if name != "index_access" || expr_call.args.len() != 2 {
            return None;
        }

        let mut args = expr_call.args.iter();
        let slice = args.next()?;
        let index = args.next()?;
        Some(ContractExpr::IndexAccess {
            slice: Box::new(Self::parse_contract_expr(
                tcx,
                def_id,
                slice,
                "index_access",
            )),
            index: Box::new(Self::parse_contract_expr(
                tcx,
                def_id,
                index,
                "index_access",
            )),
        })
    }

    fn parse_len_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let name = func_path.path.segments.last()?.ident.to_string();
        if name != "len" || expr_call.args.len() != 1 {
            return None;
        }
        let target = expr_call.args.first()?;
        Some(ContractExpr::Len(Box::new(Self::parse_contract_expr(
            tcx, def_id, target, "len",
        ))))
    }

    fn parse_layout_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let last = func_path.path.segments.last()?;
        let name = last.ident.to_string();
        if name != "size_of" && name != "align_of" {
            return None;
        }

        let ty = if let Some(arg) = expr_call.args.first() {
            Self::parse_type_opt(tcx, def_id, arg)
        } else {
            Self::parse_turbofish_type(tcx, def_id, &last.arguments, "ValidNum")
        }?;

        Some(match name.as_str() {
            "size_of" => ContractExpr::SizeOf(ty),
            "align_of" => ContractExpr::AlignOf(ty),
            _ => return None,
        })
    }

    fn parse_builtin_fn_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let name = func_path.path.segments.last()?.ident.to_string();
        match name.as_str() {
            "min" if expr_call.args.len() == 2 => {
                let a = Self::parse_contract_expr(tcx, def_id, &expr_call.args[0], "min");
                let b = Self::parse_contract_expr(tcx, def_id, &expr_call.args[1], "min");
                Some(ContractExpr::Min {
                    a: Box::new(a),
                    b: Box::new(b),
                })
            }
            "max" if expr_call.args.len() == 2 => {
                let a = Self::parse_contract_expr(tcx, def_id, &expr_call.args[0], "max");
                let b = Self::parse_contract_expr(tcx, def_id, &expr_call.args[1], "max");
                Some(ContractExpr::Max {
                    a: Box::new(a),
                    b: Box::new(b),
                })
            }
            _ => None,
        }
    }

    fn parse_turbofish_type(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        arguments: &PathArguments,
        sp: &str,
    ) -> Option<Ty<'tcx>> {
        let PathArguments::AngleBracketed(args) = arguments else {
            return None;
        };
        args.args.iter().find_map(|arg| match arg {
            GenericArgument::Type(ty) => Self::parse_syn_type(tcx, def_id, ty, sp),
            _ => None,
        })
    }

    fn parse_type_opt(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> Option<Ty<'tcx>> {
        if let Expr::Path(expr_path) = expr
            && let Some(segment) = expr_path.path.segments.last()
        {
            return match_ty_with_ident(tcx, def_id, segment.ident.to_string());
        }
        let ty_ident = access_ident_recursive(expr)?.0;
        match_ty_with_ident(tcx, def_id, ty_ident)
    }

    fn parse_syn_type(tcx: TyCtxt<'tcx>, def_id: DefId, ty: &Type, sp: &str) -> Option<Ty<'tcx>> {
        let Type::Path(type_path) = ty else {
            return None;
        };
        let ident = type_path.path.segments.last()?.ident.to_string();
        match_ty_with_ident(tcx, def_id, ident).or_else(|| {
            rap_debug!("Cannot get type in {:?} Tag from {:?}", sp, type_path);
            None
        })
    }

    fn parse_builtin_const(tcx: TyCtxt<'tcx>, expr: &Expr) -> Option<u128> {
        let Expr::Path(expr_path) = expr else {
            return None;
        };
        let mut segments = expr_path.path.segments.iter();
        let first = segments.next()?.ident.to_string();
        let second = segments.next()?.ident.to_string();
        if segments.next().is_some() || second != "MAX" {
            return None;
        }

        let pointer_bits = tcx.data_layout.pointer_size().bits();
        match first.as_str() {
            "isize" => Some((1_u128 << (pointer_bits - 1)) - 1),
            "usize" => Some((1_u128 << pointer_bits) - 1),
            _ => None,
        }
    }

    fn parse_const_param(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(expr_path) = expr else {
            return None;
        };
        let ident = expr_path.path.get_ident()?.to_string();
        let mut generics = Some(tcx.generics_of(def_id));
        while let Some(current) = generics {
            if let Some(param) = current.own_params.iter().find(|param| {
                matches!(param.kind, GenericParamDefKind::Const { .. })
                    && param.name.as_str() == ident
            }) {
                return Some(ContractExpr::ConstParam {
                    index: param.index,
                    name: ident,
                });
            }
            generics = current.parent.map(|parent| tcx.generics_of(parent));
        }
        None
    }

    fn parse_contract_place(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<ContractPlace<'tcx>> {
        // Handle .iter() / .each_element() — iterate over slice elements.
        if let Expr::MethodCall(expr_method) = expr {
            if (expr_method.method == "iter" || expr_method.method == "each_element")
                && expr_method.args.is_empty()
            {
                let mut place =
                    Self::parse_contract_place(tcx, def_id, &expr_method.receiver)?;
                place.projections.push(ContractProjection::IterElements);
                return Some(place);
            }
        }

        // Handle .unwrap_some() method call — downcast to the Some variant.
        if let Expr::MethodCall(expr_method) = expr {
            if expr_method.method == "unwrap_some" && expr_method.args.is_empty() {
                if let Some((base, fields, recv_ty)) =
                    parse_expr_into_local_and_ty(tcx, def_id, &expr_method.receiver)
                {
                    let peeled_ty = recv_ty.peel_refs();
                    if let TyKind::Adt(adt_def, _) = peeled_ty.kind() {
                        if adt_def.is_enum() {
                            let some_variant =
                                adt_def.variants().iter_enumerated().find_map(|(vidx, v)| {
                                    if v.name.to_string() == "Some" {
                                        Some(vidx.as_usize())
                                    } else {
                                        None
                                    }
                                });
                            if let Some(variant_index) = some_variant {
                                let mut projections: Vec<ContractProjection> = fields
                                    .into_iter()
                                    .map(|(index, ty)| ContractProjection::Field {
                                        index,
                                        ty: Some(ty),
                                    })
                                    .collect();
                                projections.push(ContractProjection::Downcast { variant_index });
                                let base_enum = if base == 0 {
                                    PlaceBase::Return
                                } else {
                                    PlaceBase::Local(base)
                                };
                                return Some(ContractPlace {
                                    base: base_enum,
                                    projections,
                                });
                            }
                        }
                    }
                }
            }
        }

        if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, expr) {
            return Some(ContractPlace::local(base, fields));
        }
        Self::parse_named_place(expr)
    }

    fn parse_named_place(expr: &Expr) -> Option<ContractPlace<'tcx>> {
        if let Expr::Path(expr_path) = expr {
            if let Some(ident) = expr_path.path.get_ident() {
                let s = ident.to_string();
                if let Some(num_str) = s.strip_prefix("Arg_") {
                    if let Ok(idx) = num_str.parse::<usize>() {
                        return Some(ContractPlace::arg(idx));
                    }
                }
                if s == "return" {
                    return Some(ContractPlace {
                        base: PlaceBase::Return,
                        projections: Vec::new(),
                    });
                }
            }
        }
        None
    }

    fn parse_valid_num(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Vec<NumericPredicate<'tcx>> {
        match exprs {
            [] => Vec::new(),
            [expr] => Self::parse_numeric_predicate(tcx, def_id, expr)
                .into_iter()
                .collect(),
            [value, range, ..] => {
                if let Some(predicates) = Self::parse_interval_predicates(tcx, def_id, value, range)
                {
                    predicates
                } else {
                    Self::parse_numeric_predicate(tcx, def_id, value)
                        .into_iter()
                        .collect()
                }
            }
        }
    }

    fn parse_numeric_predicate(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<NumericPredicate<'tcx>> {
        if let Expr::Binary(expr_binary) = expr {
            if let Some(op) = RelOp::from_syn(&expr_binary.op) {
                return Some(NumericPredicate::new(
                    Self::parse_contract_expr(tcx, def_id, &expr_binary.left, "ValidNum"),
                    op,
                    Self::parse_contract_expr(tcx, def_id, &expr_binary.right, "ValidNum"),
                ));
            }
        }

        // Simplify `!self.is_empty()` to `self.len() != 0`.
        if let Expr::Unary(expr_unary) = expr
            && matches!(expr_unary.op, syn::UnOp::Not(..))
        {
            if let Expr::MethodCall(expr_method) = expr_unary.expr.as_ref()
                && expr_method.method == "is_empty"
                && expr_method.args.is_empty()
            {
                return Some(NumericPredicate::new(
                    ContractExpr::Len(Box::new(Self::parse_contract_expr(
                        tcx,
                        def_id,
                        &expr_method.receiver,
                        "ValidNum",
                    ))),
                    RelOp::Ne,
                    ContractExpr::Const(0),
                ));
            }
        }

        Some(NumericPredicate::new(
            Self::parse_contract_expr(tcx, def_id, expr, "ValidNum"),
            RelOp::Ne,
            ContractExpr::Const(0),
        ))
    }

    fn parse_interval_predicates(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        value: &Expr,
        range: &Expr,
    ) -> Option<Vec<NumericPredicate<'tcx>>> {
        match range {
            Expr::Array(array) if array.elems.len() == 2 => {
                let mut elems = array.elems.iter();
                let lower = elems.next().unwrap();
                let upper = elems.next().unwrap();
                Some(Self::build_interval_predicates(
                    tcx, def_id, value, lower, true, upper, true,
                ))
            }
            Expr::Lit(expr_lit) => {
                let Lit::Str(range_lit) = &expr_lit.lit else {
                    return None;
                };
                Self::parse_string_interval(tcx, def_id, value, &range_lit.value())
            }
            _ => None,
        }
    }

    fn parse_string_interval(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        value: &Expr,
        raw_range: &str,
    ) -> Option<Vec<NumericPredicate<'tcx>>> {
        let trimmed = raw_range.trim();
        if trimmed.len() < 5 {
            return None;
        }

        let lower_inclusive = trimmed.starts_with('[');
        let upper_inclusive = trimmed.ends_with(']');
        if !(lower_inclusive || trimmed.starts_with('('))
            || !(upper_inclusive || trimmed.ends_with(')'))
        {
            return None;
        }

        let body = &trimmed[1..trimmed.len() - 1];
        let (lower_raw, upper_raw) = body.split_once(',')?;
        let lower = safety_parser::syn::parse_str::<Expr>(lower_raw.trim()).ok()?;
        let upper = safety_parser::syn::parse_str::<Expr>(upper_raw.trim()).ok()?;

        Some(Self::build_interval_predicates(
            tcx,
            def_id,
            value,
            &lower,
            lower_inclusive,
            &upper,
            upper_inclusive,
        ))
    }

    fn build_interval_predicates(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        value: &Expr,
        lower: &Expr,
        lower_inclusive: bool,
        upper: &Expr,
        upper_inclusive: bool,
    ) -> Vec<NumericPredicate<'tcx>> {
        let value_expr = Self::parse_contract_expr(tcx, def_id, value, "ValidNum");
        let lower_expr = Self::parse_contract_expr(tcx, def_id, lower, "ValidNum");
        let upper_expr = Self::parse_contract_expr(tcx, def_id, upper, "ValidNum");
        vec![
            NumericPredicate::new(
                lower_expr,
                if lower_inclusive {
                    RelOp::Le
                } else {
                    RelOp::Lt
                },
                value_expr.clone(),
            ),
            NumericPredicate::new(
                value_expr,
                if upper_inclusive {
                    RelOp::Le
                } else {
                    RelOp::Lt
                },
                upper_expr,
            ),
        ]
    }
}

/// Strip `IterElements` from a property arg and return the container place
/// (without the projection) if `IterElements` was present.
fn strip_iter_elements<'tcx>(arg: &mut PropertyArg<'tcx>) -> Option<ContractPlace<'tcx>> {
    if let PropertyArg::Place(place) = arg {
        if place.projections.iter().any(|p| matches!(p, ContractProjection::IterElements)) {
            let mut container = place.clone();
            container.projections.retain(|p| !matches!(p, ContractProjection::IterElements));
            place.projections.retain(|p| !matches!(p, ContractProjection::IterElements));
            return Some(container);
        }
    }
    None
}

/// True when `ty` denotes a slice `[T]`, possibly behind references.
/// Extract the inner type from an `Expr::Array` (the `[T]` notation in
/// `SplitTransmute([T], [U])`), then resolve it via `parse_type`.
fn unwrap_array_expr<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> Option<Ty<'tcx>> {
    if let Expr::Array(arr) = expr
        && arr.elems.len() == 1
    {
        return Property::parse_type(tcx, def_id, &arr.elems[0], "SplitTransmute");
    }
    return Property::parse_type(tcx, def_id, expr, "SplitTransmute");
}

pub(crate) fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(expr) {
        let (param_names, param_tys) = parse_signature(tcx, def_id);
        if param_names[0] != "0" {
            if let Some(param_index) = param_names.iter().position(|name| name == &base_ident) {
                return resolve_projection_from_base_ident(
                    tcx,
                    base_ident,
                    fields,
                    param_index + 1,
                    param_tys[param_index],
                );
            }
        }

        if let Some(struct_ty) = get_struct_self_ty(tcx, def_id) {
            return resolve_projection_from_struct_ident(
                tcx, def_id, base_ident, fields, struct_ty,
            );
        }
    }
    None
}

fn resolve_projection_from_base_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    _base_ident: String,
    fields: Vec<String>,
    base_local: usize,
    base_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let mut current_ty = base_ty;
    let mut field_indices = Vec::new();
    for field_name in fields {
        let Some((field_idx, field_ty)) = resolve_next_field(tcx, current_ty, &field_name) else {
            return None;
        };
        current_ty = field_ty;
        field_indices.push((field_idx, current_ty));
    }
    Some((base_local, field_indices, current_ty))
}

fn resolve_projection_from_struct_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    base_ident: String,
    fields: Vec<String>,
    struct_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let Some((field_idx, field_ty)) = resolve_next_field(tcx, struct_ty, &base_ident) else {
        return None;
    };

    let mut current_ty = field_ty;
    let mut field_indices = vec![(field_idx, current_ty)];
    for field_name in fields {
        let Some((next_field_idx, next_field_ty)) =
            resolve_next_field(tcx, current_ty, &field_name)
        else {
            return None;
        };
        current_ty = next_field_ty;
        field_indices.push((next_field_idx, current_ty));
    }

    let base_local = if get_type(tcx, def_id) == FnKind::Constructor {
        0
    } else {
        1
    };

    Some((base_local, field_indices, current_ty))
}

fn resolve_next_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ty: Ty<'tcx>,
    field_name: &str,
) -> Option<(usize, Ty<'tcx>)> {
    let peeled_ty = base_ty.peel_refs();
    if let TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
        if !adt_def.is_struct() && !adt_def.is_union() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        if let Ok(field_idx) = field_name.parse::<usize>() {
            if field_idx < variant.fields.len() {
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)].ty(tcx, arg_list);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)]
                    .ty(tcx, arg_list)
                    .skip_norm_wip();
                return Some((field_idx, field_ty));
            }
        }
        if let Some((idx, _)) = variant
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.ident(tcx).name.to_string() == field_name)
        {
            #[cfg(not(rapx_rustc_ge_198))]
            let field_ty = variant.fields[FieldIdx::from_usize(idx)].ty(tcx, arg_list);
            #[cfg(rapx_rustc_ge_198)]
            let field_ty = variant.fields[FieldIdx::from_usize(idx)]
                .ty(tcx, arg_list)
                .skip_norm_wip();
            return Some((idx, field_ty));
        }
    }
    None
}
