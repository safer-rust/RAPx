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

use std::collections::{HashMap, HashSet};
use std::sync::{OnceLock, RwLock};

use pest::iterators::Pair;
use pest::Parser;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use safety_parser::syn::visit_mut::{self, VisitMut};
use safety_parser::syn::Expr;

use super::pest_grammar::{ContractParser, Rule};
use super::types::{Property, PropertyKind};

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

/// Parse a source fragment containing block-shaped contract definitions
/// (`Name(params) { body }`) into a list of `DefSpec`s.
///
/// This is the format produced by the `pred!` macro and used by the bundled
/// `assets/*-contracts.rs` files:
///
/// ```text
/// MySafeRead(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) }
/// ```
///
/// Each def may be preceded by `///` doc lines (shown as the human-readable
/// meaning in reports); `//` comments and blank lines are skipped.  The body
/// supports `&&` (conjunction) and `||` (disjunction) of `Tag(arg, ...)` calls,
/// plus `( ... )` grouping for a conjunction used as a single disjunct.
pub fn parse_defs(source: &str) -> Vec<DefSpec> {
    let mut defs = Vec::new();
    let mut doc: Vec<String> = Vec::new();

    let mut s = source.trim_start();
    loop {
        // Skip blank lines and `//` comments; collect `///` doc lines.
        loop {
            if let Some(r) = s.strip_prefix("///") {
                let end = r.find('\n').unwrap_or(r.len());
                doc.push(r[..end].trim().to_string());
                s = r[end..].trim_start();
            } else if let Some(r) = s.strip_prefix("//") {
                let end = r.find('\n').unwrap_or(r.len());
                s = r[end..].trim_start();
            } else {
                break;
            }
        }
        if s.is_empty() {
            break;
        }

        let (Some(mut def), consumed) = parse_one_def_block(s) else {
            break;
        };
        def.doc = std::mem::take(&mut doc);
        defs.push(def);
        s = s[consumed..].trim_start();
    }

    defs
}

/// Parse a single leading `Name(p: Ptr, T: Ty, ...) { body }` block from `s`.
/// Returns the `DefSpec` (without doc) and the number of bytes consumed through
/// the closing `}`.
///
/// The block is emitted by the `pred!` proc-macro as a single line of
/// space-separated tokens, so parameter names and role annotations (`Ptr`,
/// `Ty`, `Expr`, `Ident`) are split on `:` and `,` after trimming whitespace.
/// The braces delimit the body, so nested `==`/`<=` inside a `ValidNum`
/// predicate cannot be confused with a definition separator.
fn parse_one_def_block(s: &str) -> (Option<DefSpec>, usize) {
    let Some(open) = s.find('(') else {
        return (None, 0);
    };
    let name = s[..open].trim().to_string();
    if name.is_empty() {
        return (None, 0);
    }

    // Params: match the first `)` — parameter annotations are `ident: ident`,
    // so they never contain nested parens.
    let Some(rel_close) = s[open + 1..].find(')') else {
        return (None, 0);
    };
    let close = open + 1 + rel_close;
    let params_str = &s[open + 1..close];

    // Expect a `{` after the parameter list.
    let after = s[close + 1..].trim_start();
    if !after.starts_with('{') {
        return (None, 0);
    }
    let brace_open = s.len() - after.len();
    let body_start = brace_open + 1;

    // Match braces to the closing `}` (the body may contain `if { } else { }`).
    let bytes = s.as_bytes();
    let mut depth = 1usize;
    let mut j = body_start;
    while j < bytes.len() {
        match bytes[j] {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        j += 1;
    }
    if depth != 0 {
        return (None, 0);
    }
    let body = s[body_start..j].trim();

    let (params, param_tys) = parse_equation_params(params_str);
    let Some(body_ast) = parse_body(body, &params) else {
        return (None, 0);
    };

    let def = DefSpec {
        name,
        params,
        param_tys,
        body: body_ast,
        doc: Vec::new(),
    };
    (Some(def), j + 1)
}

fn parse_equation_params(params_str: &str) -> (Vec<String>, Vec<String>) {
    let mut params = Vec::new();
    let mut param_tys = Vec::new();
    for seg in params_str.split(',') {
        let seg = seg.trim();
        if seg.is_empty() {
            continue;
        }
        match seg.split_once(':') {
            Some((p, ty)) => {
                params.push(p.trim().to_string());
                param_tys.push(ty.trim().to_string());
            }
            None => {
                params.push(seg.to_string());
                param_tys.push(String::new());
            }
        }
    }
    (params, param_tys)
}

/// Render a `syn::Expr` back to source-like text.  `proc_macro2` stringifies
/// tokens space-separated (`self . 0`, `size_of (T)`), so collapse the spaces
/// around punctuation for a readable form.
fn render_expr_src(e: &Expr) -> String {
    quote::ToTokens::to_token_stream(e)
        .to_string()
        .replace(" . ", ".")
        .replace(" ,", ",")
        .replace(" (", "(")
        .replace(" :: ", "::")
}

/// Resolve a call-site argument expression to its display form, following the
/// def parameter's declared role so internal placeholders (e.g. `Arg_0` from a
/// JSON contract) render as the actual parameter name.
fn resolve_arg_string<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    param_ty: &str,
    expr: &Expr,
) -> String {
    match param_ty {
        "Ptr" => super::resolve::parse_target_arg(tcx, def_id, expr)
            .display_for_report(tcx, None, Some(def_id)),
        "Ty" => super::resolve::parse_type(tcx, def_id, expr, "def")
            .map(|ty| ty.to_string())
            .unwrap_or_else(|| render_expr_src(expr)),
        "Expr" => {
            let ce = super::resolve::expr_to_pest(tcx, def_id, expr);
            super::render::display_expr_user_friendly(&ce, tcx, None, Some(def_id))
        }
        _ => render_expr_src(expr),
    }
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
/// already a conjunction); `or` produces a single `Property::Or` property
/// whose `groups` encode the DNF groups.
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
            vec![Property::new_or(groups)]
        }
        DefBody::Call { tag, args } => {
            // Validate the def's parameter annotations against the primitive's
            // declared argument roles (e.g. a `Ptr` param used in a `Ty` slot).
            if let Some(spec) = super::spec::find_spec(tag) {
                match spec.build {
                    // Variadic target list (Alias/Alive): every param must be Ptr.
                    super::spec::BuildKind::Targets => {
                        for (pos, a) in args.iter().enumerate() {
                            if let DefArg::Param(i) = a
                                && let Some(def_ty) = param_tys.get(*i)
                                && !def_ty_matches_arg_kind(
                                    def_ty,
                                    super::spec::ArgKind::Target,
                                )
                            {
                                let pname = params.get(*i).map(String::as_str).unwrap_or("?");
                                rap_warn!(
                                    "contract def type mismatch: `{tag}` arg {pos} expects \
                                     {:?}, but param `{pname}` is annotated `{def_ty}`",
                                    super::spec::ArgKind::Target
                                );
                            }
                        }
                    }
                    // Accepts-anything placeholder: no constraints.
                    super::spec::BuildKind::TobeSpecified => {}
                    // Fixed-arity tag: match a form by call arity, then check each
                    // positional parameter annotation against the declared role.
                    _ => {
                        if let Some(form) = spec.forms.iter().find(|f| f.len() == args.len()) {
                            for (pos, a) in args.iter().enumerate() {
                                if let DefArg::Param(i) = a
                                    && let (Some(def_ty), Some(&arg_kind)) =
                                        (param_tys.get(*i), form.get(pos))
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
    Property::new_leaf(PropertyKind::Unknown, Vec::new())
}

// ── Registry ───────────────────────────────────────────────────

/// Builtin defs shipped with `rapx`: the standard compound safety properties
/// (`std-contracts.rs`) plus user extensions (`user-contracts.rs`).  Immutable
/// and shared across every crate.
fn builtin_defs_map() -> &'static HashMap<String, DefSpec> {
    static BUILTIN: OnceLock<HashMap<String, DefSpec>> = OnceLock::new();
    BUILTIN.get_or_init(builtin_defs)
}

/// Per-crate user defs, registered from `#[rapx::def_contract]` attributes.
///
/// Keyed by `CrateNum` so that defs defined in one crate cannot leak into (or
/// collide with) another crate analyzed in the same process.  A crate's own
/// defs shadow builtin defs of the same name.
fn user_defs_map() -> &'static RwLock<HashMap<CrateNum, HashMap<String, DefSpec>>> {
    static USER: OnceLock<RwLock<HashMap<CrateNum, HashMap<String, DefSpec>>>> = OnceLock::new();
    USER.get_or_init(|| RwLock::new(HashMap::new()))
}

/// Builtin defs shipped with `rapx`: the standard compound safety properties
/// (`std-contracts.rs`) plus user extensions (`user-contracts.rs`).
fn builtin_defs() -> HashMap<String, DefSpec> {
    let mut map = HashMap::new();
    for def in parse_defs(include_str!("assets/std-contracts.rs")) {
        map.insert(def.name.clone(), def);
    }
    for def in parse_defs(include_str!("assets/user-contracts.rs")) {
        map.insert(def.name.clone(), def);
    }
    map
}

/// Look up a `def` by name, in the given crate's namespace first, then the
/// builtin namespace.
pub fn find_def(krate: CrateNum, name: &str) -> Option<DefSpec> {
    if let Some(d) = user_defs_map()
        .read()
        .ok()
        .and_then(|t| t.get(&krate).and_then(|m| m.get(name).cloned()))
    {
        return Some(d);
    }
    builtin_defs_map().get(name).cloned()
}

/// Expand a named def against concrete argument expressions.
pub fn expand_def<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    name: &str,
    exprs: &[Expr],
) -> Option<Vec<Property<'tcx>>> {
    let def = find_def(def_id.krate, name)?;
    if def.params.len() != exprs.len() {
        return None;
    }
    // Guard against self-referential defs (direct or mutual) before recursing;
    // otherwise `expand_body` → `Property::parse_list` → `expand_def` would
    // recurse forever and overflow the stack.
    if let Some(cycle) = find_def_cycle(def_id.krate, name) {
        rap_error!("contract def cycle detected: {}", cycle.join(" -> "));
        return None;
    }
    let mut props = expand_body(tcx, def_id, &def.body, exprs, &def.params, &def.param_tys);
    // Tag expanded properties with the def name, its full call-site arguments,
    // and its doc-derived meaning so reports can show the compound as a single
    // entry instead of the underlying primitives.
    let arg_strings: Vec<String> = exprs
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let param_ty = def.param_tys.get(i).map(|s| s.as_str()).unwrap_or("");
            resolve_arg_string(tcx, def_id, param_ty, e)
        })
        .collect();
    let meaning = if def.doc.is_empty() {
        None
    } else {
        Some(def.doc.join(" "))
    };
    for p in &mut props {
        p.set_origin(name.to_string(), arg_strings.clone(), meaning.clone());
    }
    Some(props)
}

/// Return a cycle path (e.g. `["A", "B", "A"]`) if expanding `start` can reach
/// itself again through def-to-def references, `None` otherwise.
///
/// Only edges that resolve to another registered def are followed; calls to
/// primitives (`Allocated`, `Align`, ...) terminate the walk.  The crate's own
/// defs are overlaid on the builtin namespace.
pub fn find_def_cycle(krate: CrateNum, start: &str) -> Option<Vec<String>> {
    let mut combined = builtin_defs_map().clone();
    if let Ok(user) = user_defs_map().read()
        && let Some(crate_defs) = user.get(&krate)
    {
        for (name, def) in crate_defs {
            combined.insert(name.clone(), def.clone());
        }
    }
    find_cycle_in(start, &combined)
}

fn find_cycle_in(start: &str, table: &HashMap<String, DefSpec>) -> Option<Vec<String>> {
    fn dfs(
        name: &str,
        table: &HashMap<String, DefSpec>,
        path: &mut Vec<String>,
        done: &mut HashSet<String>,
    ) -> Option<Vec<String>> {
        if let Some(pos) = path.iter().position(|n| n == name) {
            let mut cycle: Vec<String> = path[pos..].to_vec();
            cycle.push(name.to_string());
            return Some(cycle);
        }
        if done.contains(name) {
            return None;
        }
        let Some(def) = table.get(name) else {
            return None;
        };
        path.push(name.to_string());
        for tag in def_refs(&def.body) {
            if let Some(cycle) = dfs(&tag, table, path, done) {
                return Some(cycle);
            }
        }
        path.pop();
        done.insert(name.to_string());
        None
    }

    let mut path = Vec::new();
    let mut done = HashSet::new();
    dfs(start, table, &mut path, &mut done)
}

/// Collect the tag names referenced by a `DefBody`, in left-to-right order.
fn def_refs(body: &DefBody) -> Vec<String> {
    let mut out = Vec::new();
    collect_def_refs(body, &mut out);
    out
}

fn collect_def_refs(body: &DefBody, out: &mut Vec<String>) {
    match body {
        DefBody::And(parts) | DefBody::Or(parts) => {
            for part in parts {
                collect_def_refs(part, out);
            }
        }
        DefBody::Call { tag, .. } => out.push(tag.clone()),
    }
}

// ── Registration of user-defined defs ─────────────────────────

/// Parse `def` declarations from `source` and insert them into the given
/// crate's namespace.  Returns the number of defs registered.
pub fn register_defs_from_source(krate: CrateNum, source: &str) -> usize {
    let defs = parse_defs(source);
    let n = defs.len();
    if n == 0 {
        return 0;
    }
    let mut table = user_defs_map().write().expect("def table poisoned");
    let entry = table.entry(krate).or_default();
    for def in defs {
        entry.insert(def.name.clone(), def);
    }
    n
}

// ── Procedural-macro contract definitions ─────────────────────

/// Scan the local crate for `#[rapx::def_contract("...")]` tool attributes
/// (emitted by the `rapx_macros::pred` proc-macro) and register each embedded
/// `def` string.  Returns the number of defs registered.
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
                    let n = register_defs_from_source(LOCAL_CRATE, &def_str);
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

