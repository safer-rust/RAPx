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

use safety_parser::syn::Expr;

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
    let body = body.trim();
    let or_parts = split_top_level(body, "||");
    if or_parts.len() > 1 {
        let mut children = Vec::new();
        for part in or_parts {
            children.push(parse_body(&part, params)?);
        }
        return Some(DefBody::Or(children));
    }

    let and_parts = split_top_level(body, "&&");
    if and_parts.len() > 1 {
        let mut children = Vec::new();
        for part in and_parts {
            children.push(parse_body(&part, params)?);
        }
        return Some(DefBody::And(children));
    }

    parse_call(body, params)
}

/// Split on `sep` at the top level (ignoring occurrences inside parentheses).
fn split_top_level(s: &str, sep: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    let bytes = s.as_bytes();
    let mut i = 0usize;
    while i < bytes.len() {
        let ch = bytes[i] as char;
        match ch {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            _ => {}
        }
        if depth == 0 && s[i..].starts_with(sep) {
            parts.push(s[start..i].trim().to_string());
            i += sep.len();
            start = i;
            continue;
        }
        i += 1;
    }
    parts.push(s[start..].trim().to_string());
    parts.retain(|p| !p.is_empty());
    parts
}

/// Parse a single `Tag(arg, ...)` call, or a parenthesised conjunction.
fn parse_call(s: &str, params: &[String]) -> Option<DefBody> {
    let s = s.trim();

    // Strip one level of surrounding parentheses (used for `(A && B)` disjuncts).
    if let Some(inner) = strip_outer_parens(s) {
        return parse_body(inner, params);
    }

    let open = s.find('(')?;
    let tag = s[..open].trim().to_string();
    let close = s.rfind(')')?;
    if open >= close {
        return None;
    }
    let args_raw = &s[open + 1..close];

    let args = if args_raw.trim().is_empty() {
        Vec::new()
    } else {
        args_raw
            .split(',')
            .map(|a| a.trim().to_string())
            .filter(|a| !a.is_empty())
            .map(|tok| resolve_arg(&tok, params))
            .collect()
    };

    Some(DefBody::Call { tag, args })
}

/// Classify a body argument token as a formal-parameter reference or a literal.
fn resolve_arg(token: &str, params: &[String]) -> DefArg {
    if let Some(i) = params.iter().position(|n| n == token) {
        DefArg::Param(i)
    } else {
        DefArg::Lit(token.to_string())
    }
}

/// Strip outer parentheses only when they enclose the whole expression.
fn strip_outer_parens(s: &str) -> Option<&str> {
    let t = s.trim();
    if t.starts_with('(') && t.ends_with(')') {
        let inner = &t[1..t.len() - 1];
        if parens_balanced(inner) {
            return Some(inner.trim());
        }
    }
    None
}

fn parens_balanced(s: &str) -> bool {
    let mut depth = 0isize;
    for ch in s.chars() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            _ => {}
        }
    }
    depth == 0
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
                    DefArg::Lit(s) => match syn::parse_str::<Expr>(s) {
                        Ok(e) => resolved.push(e),
                        Err(_) => return vec![unknown_property()],
                    },
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
