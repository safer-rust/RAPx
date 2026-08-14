//! User-defined contract `def` layer.
//!
//! Users (downloading a prebuilt `rapx` binary) can define *new* named safety
//! contracts as boolean combinations of the 21 primitive safety properties, and
//! reference them from `#[rapx::requires(MyTag(...))]` — without recompiling
//! `rapx`.
//!
//! A `def` is a DNF macro over primitive property calls:
//!
//! ```text
//! def MySafeRead(p: Target, T: Ty, n: Expr) =
//!     NonNull(p) && Align(p, T) && Allocated(p, T, n);
//!
//! def StrOrBytes(s: Target, T: Ty, n: Expr) =
//!     ValidCStr(s, n) || (Allocated(s, T, n) && Init(s, T, n));
//! ```
//!
//! The DSL only *composes* existing primitives; it cannot invent new primitive
//! semantics (those live in `property_checker.rs`).  Expansion is a pure
//! front-end that produces ordinary `Property` values consumed by the existing
//! checker.

use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};

use pest::iterators::Pair;
use pest::Parser;
use safety_parser::syn::visit_mut::{self, VisitMut};
use safety_parser::syn::Expr;

use super::pest_grammar::{ContractParser, Rule};
use super::types::{ContractKind, Property, PropertyKind};

/// A single argument in a `def` body: a reference to a formal parameter, or a
/// literal (kept as source text, re-parsed as `syn::Expr` at expansion time).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefArg {
    Param(usize),
    Lit(String),
}

/// The body of a `def`, structured as DNF (Or of And of calls).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefBody {
    And(Vec<DefBody>),
    Or(Vec<DefBody>),
    Call { tag: String, args: Vec<DefArg> },
}

/// A parsed `def` declaration.
#[derive(Debug, Clone)]
pub struct DefSpec {
    pub name: String,
    pub params: Vec<String>,
    pub param_tys: Vec<String>,
    pub body: DefBody,
    pub doc: Vec<String>,
}

/// Parse a source fragment containing `fn`-shaped contract definitions into a
/// list of `DefSpec`s.
///
/// Each contract is a Rust function signature whose body is a boolean
/// combination of primitive property calls:
///
/// ```text
/// fn MySafeRead(p: Target, T: Ty, n: Expr) -> bool {
///     NonNull(p) && Align(p, T) && Allocated(p, T, n)
/// }
/// ```
///
/// `//` comments and non-`fn` items are skipped.  The body supports `&&`
/// (conjunction) and `||` (disjunction) of `Tag(arg, ...)` calls, plus `( ... )`
/// grouping for a conjunction used as a single disjunct.
pub fn parse_defs(source: &str) -> Vec<DefSpec> {
    let file: ::syn::File = match ::syn::parse_str(source) {
        Ok(f) => f,
        Err(_) => return Vec::new(),
    };

    let mut defs = Vec::new();
    for item in file.items {
        let ::syn::Item::Fn(f) = item else { continue };
        let Some(def) = parse_one_def(&f) else { continue };
        defs.push(def);
    }
    defs
}

fn parse_one_def(f: &::syn::ItemFn) -> Option<DefSpec> {
    use quote::ToTokens;

    let name = f.sig.ident.to_string();

    let mut params = Vec::new();
    let mut param_tys = Vec::new();
    for arg in &f.sig.inputs {
        let ::syn::FnArg::Typed(pt) = arg else { continue };
        let pname = pt.pat.to_token_stream().to_string().replace(' ', "");
        let pty = pt.ty.to_token_stream().to_string().replace(' ', "");
        params.push(pname);
        param_tys.push(pty);
    }

    // Serialize the body expression(s), stripping trailing `;` so the result
    // is a plain boolean expression.
    let mut body_parts = Vec::new();
    for stmt in &f.block.stmts {
        let mut s = stmt.to_token_stream().to_string();
        if let Some(stripped) = s.strip_suffix(';') {
            s = stripped.to_string();
        }
        let s = s.trim().to_string();
        if !s.is_empty() {
            body_parts.push(s);
        }
    }
    let body_str = body_parts.join(" ");

    let body = parse_body(&body_str, &params)?;

    Some(DefSpec {
        name,
        params,
        param_tys,
        body,
        doc: Vec::new(),
    })
}

/// Parse the body into a DNF tree.  `||` binds looser than `&&`.
fn parse_body(body: &str, params: &[String]) -> Option<DefBody> {
    let mut pairs = ContractParser::parse(Rule::def_body, body).ok()?;
    let def_body = pairs.next()?;
    let or_expr = def_body.into_inner().next()?;
    Some(conv_def_or(or_expr, params))
}

fn conv_def_or(pair: Pair<Rule>, params: &[String]) -> DefBody {
    let parts: Vec<DefBody> = pair.into_inner().map(|p| conv_def_and(p, params)).collect();
    if parts.len() == 1 {
        parts.into_iter().next().unwrap()
    } else {
        DefBody::Or(parts)
    }
}

fn conv_def_and(pair: Pair<Rule>, params: &[String]) -> DefBody {
    let parts: Vec<DefBody> = pair.into_inner().map(|p| conv_def_leaf(p, params)).collect();
    if parts.len() == 1 {
        parts.into_iter().next().unwrap()
    } else {
        DefBody::And(parts)
    }
}

fn conv_def_leaf(pair: Pair<Rule>, params: &[String]) -> DefBody {
    match pair.into_inner().next() {
        Some(inner) => match inner.as_rule() {
            Rule::tag_call => conv_def_call(inner, params),
            Rule::or_expr => conv_def_or(inner, params),
            _ => DefBody::Call {
                tag: String::new(),
                args: Vec::new(),
            },
        },
        None => DefBody::Call {
            tag: String::new(),
            args: Vec::new(),
        },
    }
}

fn conv_def_call(pair: Pair<Rule>, params: &[String]) -> DefBody {
    let mut inner = pair.into_inner();
    let Some(tag) = inner.next() else {
        return DefBody::Call {
            tag: String::new(),
            args: Vec::new(),
        };
    };
    let tag = tag.as_str().to_string();
    let args = match inner.next() {
        Some(arg_list) => arg_list
            .into_inner()
            .map(|arg| {
                let text = arg.as_str().trim().to_string();
                match params.iter().position(|n| n == &text) {
                    Some(i) => DefArg::Param(i),
                    None => DefArg::Lit(text),
                }
            })
            .collect(),
        None => Vec::new(),
    };
    DefBody::Call { tag, args }
}

/// Substitute def formal parameters with the concrete call-site arguments inside
/// a literal expression (e.g. turn `size_of(T) * n` into `size_of(u32) * len`,
/// or `p.unwrap_some()` into `head.unwrap_some()`).
///
/// Only a bare single-segment path that exactly matches a formal parameter name
/// is replaced, so builtin function names (`size_of`), method names
/// (`unwrap_some`) and field names are never rewritten.
struct Subst<'a> {
    params: &'a [String],
    args: &'a [Expr],
}

impl VisitMut for Subst<'_> {
    fn visit_expr_mut(&mut self, node: &mut Expr) {
        if let Expr::Path(path) = node {
            if path.qself.is_none()
                && path.path.leading_colon.is_none()
                && path.path.segments.len() == 1
            {
                let ident = path.path.segments[0].ident.to_string();
                if let Some(i) = self.params.iter().position(|n| *n == ident) {
                    if let Some(arg) = self.args.get(i) {
                        // The substituted argument comes from the call site and
                        // never refers to this def's formals, so stop recursing.
                        *node = arg.clone();
                        return;
                    }
                }
            }
        }
        visit_mut::visit_expr_mut(self, node);
    }
}

/// Whether a def parameter annotation matches a primitive argument role.
fn def_ty_matches_arg_kind(def_ty: &str, kind: super::spec::ArgKind) -> bool {
    use super::spec::ArgKind;
    match (def_ty, kind) {
        ("Ptr", ArgKind::Target) => true,
        ("Ty", ArgKind::Ty) => true,
        ("Expr", ArgKind::Expr) => true,
        ("Ident", ArgKind::Ident) => true,
        _ => false,
    }
}

/// Expand a `DefBody` into the property list it denotes.
///
/// `and` produces multiple `Property` values (the caller's `requires` list is
/// already a conjunction); `or` produces a single `PropertyKind::Or` property
/// whose `or_alternatives` encode the DNF groups.
fn expand_body<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    body: &DefBody,
    exprs: &[Expr],
    params: &[String],
    param_tys: &[String],
) -> Vec<Property<'tcx>> {
    match body {
        DefBody::And(parts) => parts
            .iter()
            .flat_map(|p| expand_body(tcx, def_id, p, exprs, params, param_tys))
            .collect(),
        DefBody::Or(parts) => {
            let mut groups: Vec<Vec<Box<Property<'tcx>>>> = Vec::new();
            for part in parts {
                let group: Vec<Box<Property<'tcx>>> =
                    expand_body(tcx, def_id, part, exprs, params, param_tys)
                        .into_iter()
                        .map(Box::new)
                        .collect();
                if !group.is_empty() {
                    groups.push(group);
                }
            }
            vec![Property {
                kind: PropertyKind::Or,
                args: Vec::new(),
                contract_kind: ContractKind::Precond,
                null_guard: None,
                or_alternatives: groups,
                for_each: None,
                origin_name: None,
            }]
        }
        DefBody::Call { tag, args } => {
            // Validate the def's parameter annotations against the primitive's
            // declared argument roles (e.g. a `Ptr` param used in a `Ty` slot).
            if let Some(spec) = super::spec::find_spec(tag) {
                for (pos, a) in args.iter().enumerate() {
                    if let DefArg::Param(i) = a
                        && let (Some(def_ty), Some(&arg_kind)) =
                            (param_tys.get(*i), spec.args.get(pos))
                        && !def_ty_matches_arg_kind(def_ty, arg_kind)
                    {
                        let pname = params.get(*i).map(String::as_str).unwrap_or("?");
                        rap_warn!(
                            "contract def type mismatch: `{tag}` arg {pos} expects \
                             {:?}, but param `{pname}` is annotated `{def_ty}`",
                            arg_kind
                        );
                    }
                }
            }

            let mut resolved: Vec<Expr> = Vec::with_capacity(args.len());
            for a in args {
                match a {
                    DefArg::Param(i) => {
                        let Some(e) = exprs.get(*i) else {
                            return vec![unknown_property()];
                        };
                        resolved.push(e.clone());
                    }
                    DefArg::Lit(s) => {
                        let Ok(mut e) = syn::parse_str::<Expr>(s) else {
                            return vec![unknown_property()];
                        };
                        Subst { params, args: exprs }.visit_expr_mut(&mut e);
                        resolved.push(e);
                    }
                }
            }
            // Recurse through the normal property parser so nested defs and
            // primitives are handled uniformly.
            Property::parse_list(tcx, def_id, tag, &resolved)
        }
    }
}

fn unknown_property<'tcx>() -> Property<'tcx> {
    Property {
        kind: PropertyKind::Unknown,
        args: Vec::new(),
        contract_kind: ContractKind::Precond,
        null_guard: None,
        or_alternatives: Vec::new(),
        for_each: None,
        origin_name: None,
    }
}

/// Expand a body into plain DNF `(tag, args)` structure, with parameters
/// substituted by their string representations.  Used for tests and for the
/// `contract show` expansion display.
pub fn expand_body_plain(body: &DefBody, exprs: &[String]) -> Vec<Vec<(String, Vec<String>)>> {
    match body {
        DefBody::And(parts) => {
            let mut group: Vec<(String, Vec<String>)> = Vec::new();
            for part in parts {
                for g in expand_body_plain(part, exprs) {
                    group.extend(g);
                }
            }
            vec![group]
        }
        DefBody::Or(parts) => parts
            .iter()
            .flat_map(|p| expand_body_plain(p, exprs))
            .collect(),
        DefBody::Call { tag, args } => {
            let resolved: Vec<String> = args
                .iter()
                .map(|a| match a {
                    DefArg::Param(i) => exprs.get(*i).cloned().unwrap_or_default(),
                    DefArg::Lit(s) => s.clone(),
                })
                .collect();
            vec![vec![(tag.clone(), resolved)]]
        }
    }
}

// ── Global registry ────────────────────────────────────────────

/// The combined builtin + user-loaded def table, keyed by name.
fn def_table() -> &'static RwLock<HashMap<String, DefSpec>> {
    static TABLE: OnceLock<RwLock<HashMap<String, DefSpec>>> = OnceLock::new();
    TABLE.get_or_init(|| RwLock::new(builtin_defs()))
}

/// Builtin defs shipped with `rapx`: the standard compound safety properties
/// (`std-contracts.rs`) plus user extensions (`user-contracts.rs`).
fn builtin_defs() -> HashMap<String, DefSpec> {
    let mut map = HashMap::new();
    for def in parse_defs(include_str!("../source/assets/std-contracts.rs")) {
        map.insert(def.name.clone(), def);
    }
    for def in parse_defs(include_str!("../source/assets/user-contracts.rs")) {
        map.insert(def.name.clone(), def);
    }
    map
}

/// Look up a `def` by name.
pub fn find_def(name: &str) -> Option<DefSpec> {
    def_table()
        .read()
        .ok()
        .and_then(|t| t.get(name).cloned())
}

/// Expand a named def against concrete argument expressions.
pub fn expand_def<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    name: &str,
    exprs: &[Expr],
) -> Option<Vec<Property<'tcx>>> {
    let def = find_def(name)?;
    if def.params.len() != exprs.len() {
        return None;
    }
    let mut props = expand_body(tcx, def_id, &def.body, exprs, &def.params, &def.param_tys);
    // Tag expanded properties with the def name so reports show the original
    // compound contract (e.g. "Deref") instead of the underlying primitives.
    for p in &mut props {
        p.origin_name = Some(name.to_string());
    }
    Some(props)
}

// ── Registration of user-defined defs ─────────────────────────

/// Parse `def` declarations from `source` and insert them into the global def
/// table.  Returns the number of defs registered.
pub fn register_defs_from_source(source: &str) -> usize {
    let defs = parse_defs(source);
    let n = defs.len();
    if n == 0 {
        return 0;
    }
    let mut table = def_table().write().expect("def table poisoned");
    for def in defs {
        table.insert(def.name.clone(), def);
    }
    n
}

// ── Procedural-macro contract definitions ─────────────────────

/// Scan the local crate for `#[rapx::def_contract("...")]` tool attributes
/// (emitted by the `rapx_macros::def_contract` proc-macro) and register each
/// embedded `def` string.  Returns the number of defs registered.
pub fn register_contract_defs(tcx: rustc_middle::ty::TyCtxt<'_>) -> usize {
    struct Visitor<'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        count: usize,
    }

    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Visitor<'tcx> {
        fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
            let attrs = self.tcx.hir_attrs(item.hir_id());
            for attr in attrs {
                if !is_contract_def_attr(attr) {
                    continue;
                }
                let attr_str = crate::compat::attribute_to_string(self.tcx, attr);
                if let Some(def_str) = extract_contract_def_string(&attr_str) {
                    let n = register_defs_from_source(&def_str);
                    if n > 0 {
                        rap_info!("rapx: registered {n} contract def(s) from #[rapx::def_contract]");
                    }
                    self.count += n;
                }
            }
            rustc_hir::intravisit::walk_item(self, item);
        }
    }

    let mut v = Visitor { tcx, count: 0 };
    tcx.hir_visit_all_item_likes_in_crate(&mut v);
    v.count
}

/// Whether an attribute path is `rapx::def_contract` (or the bare form with the
/// tool prefix stripped).
fn is_contract_def_attr(attr: &rustc_hir::Attribute) -> bool {
    let path = attr.path();
    if path.len() >= 2
        && path[path.len() - 2].as_str() == "rapx"
        && path[path.len() - 1].as_str() == "def_contract"
    {
        return true;
    }
    path.len() == 1 && path[0].as_str() == "def_contract"
}

/// Extract the string literal from a `#[rapx::def_contract("def ...")]`
/// attribute's textual representation.
fn extract_contract_def_string(attr_str: &str) -> Option<String> {
    struct OneAttr {
        attr: syn::Attribute,
    }
    impl syn::parse::Parse for OneAttr {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let attrs = syn::Attribute::parse_outer(input)?;
            let attr = attrs
                .into_iter()
                .next()
                .ok_or_else(|| input.error("expected one attribute"))?;
            Ok(OneAttr { attr })
        }
    }

    let one: OneAttr = syn::parse_str(attr_str).ok()?;
    let syn::Meta::List(list) = one.attr.meta else {
        return None;
    };
    let lit: syn::LitStr = syn::parse2(list.tokens).ok()?;
    Some(lit.value())
}
