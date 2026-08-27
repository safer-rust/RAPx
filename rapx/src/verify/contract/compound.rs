//! User-defined compound-contract layer.
//!
//! Users (downloading a prebuilt `rapx` binary) can define *new* named safety
//! contracts as boolean combinations of the primitive safety properties, and
//! reference them from `#[rapx::requires(MyTag(...))]` — without recompiling
//! `rapx`.
//!
//! A compound property is a DNF macro over primitive property calls:
//!
//! ```text
//! MySafeRead(p: Ptr, T: Ty, n: Expr) {
//!     NonNull(p) && Align(p, T) && Allocated(p, T, n)
//! }
//!
//! StrOrBytes(s: Ptr, T: Ty, n: Expr) {
//!     ValidCStr(s, n) || (Allocated(s, T, n) && Init(s, T, n))
//! }
//! ```
//!
//! The DSL only *composes* existing primitives; it cannot invent new primitive
//! semantics (those live in `property_checker.rs`).  Expansion is a pure
//! front-end that produces ordinary `Property` values consumed by the existing
//! checker.

use std::collections::{HashMap, HashSet};
use std::sync::{OnceLock, RwLock};

use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use syn::visit_mut::{self, VisitMut};
use syn::Expr;

use super::types::{Property, PropertyKind};

/// A single argument in a compound body: a reference to a formal parameter, or a
/// literal (kept as source text, re-parsed as `syn::Expr` at expansion time).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompoundArg {
    Param(usize),
    Lit(String),
}

/// The body of a compound property, structured as DNF (Or of And of calls).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompoundBody {
    And(Vec<CompoundBody>),
    Or(Vec<CompoundBody>),
    Call { tag: String, args: Vec<CompoundArg> },
}

/// A parsed compound-property declaration.
#[derive(Debug, Clone)]
pub struct CompoundSpec {
    pub name: String,
    pub params: Vec<String>,
    pub param_tys: Vec<String>,
    pub body: CompoundBody,
    pub doc: Vec<String>,
}

/// Parse a source fragment containing block-shaped contract definitions
/// (`Name(params) { body }`) into a list of `CompoundSpec`s.
///
/// This is the format produced by the `pred!` macro and used by the bundled
/// `assets/*-compound-properties.rs` files:
///
/// ```text
/// MySafeRead(p: Ptr, T: Ty, n: Expr) { NonNull(p) && Align(p, T) && Allocated(p, T, n) }
/// ```
///
/// Each compound may be preceded by `///` doc lines (shown as the human-readable
/// meaning in reports); `//` comments and blank lines are skipped.  The body
/// supports `&&` (conjunction) and `||` (disjunction) of `Tag(arg, ...)` calls,
/// plus `( ... )` grouping for a conjunction used as a single disjunct.
pub fn parse_compounds(source: &str) -> Vec<CompoundSpec> {
    let mut compounds = Vec::new();
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

        let (Some(mut compound), consumed) = parse_one_compound_block(s) else {
            let preview: String = s.chars().take(80).collect();
            rap_error!("failed to parse contract compound near: {preview}");
            break;
        };
        compound.doc = std::mem::take(&mut doc);
        compounds.push(compound);
        s = s[consumed..].trim_start();
    }

    compounds
}

/// Parse a single leading `Name(p: Ptr, T: Ty, ...) { body }` block from `s`.
/// Returns the `CompoundSpec` (without doc) and the number of bytes consumed through
/// the closing `}`.
///
/// The block is emitted by the `pred!` proc-macro as a single line of
/// space-separated tokens, so parameter names and role annotations (`Ptr`,
/// `Ty`, `Expr`, `Ident`) are split on `:` and `,` after trimming whitespace.
/// The braces delimit the body, so nested `==`/`<=` inside a `ValidNum`
/// predicate cannot be confused with a definition separator.
fn parse_one_compound_block(s: &str) -> (Option<CompoundSpec>, usize) {
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
    let Some(body_ast) = super::pest_conv::parse_compound_body(body, &params) else {
        return (None, 0);
    };

    let compound = CompoundSpec {
        name,
        params,
        param_tys,
        body: body_ast,
        doc: Vec::new(),
    };
    (Some(compound), j + 1)
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
/// compound parameter's declared role so internal placeholders (e.g. `Arg_0` from a
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
        "Ty" => super::resolve::parse_type(tcx, def_id, expr, "compound")
            .map(|ty| ty.to_string())
            .unwrap_or_else(|| render_expr_src(expr)),
        "Expr" => {
            let ce = super::resolve::expr_to_pest(tcx, def_id, expr);
            super::render::display_expr_user_friendly(&ce, tcx, None, Some(def_id))
        }
        _ => render_expr_src(expr),
    }
}

/// Substitute compound formal parameters with the concrete call-site arguments inside
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
                        // never refers to this compound's formals, so stop recursing.
                        *node = arg.clone();
                        return;
                    }
                }
            }
        }
        visit_mut::visit_expr_mut(self, node);
    }
}

/// Whether a compound parameter annotation matches a primitive argument role.
fn compound_param_ty_matches_arg_kind(def_ty: &str, kind: super::spec::ArgKind) -> bool {
    use super::spec::ArgKind;
    match (def_ty, kind) {
        ("Ptr", ArgKind::Target) => true,
        ("Ty", ArgKind::Ty) => true,
        ("Expr", ArgKind::Expr) => true,
        ("Ident", ArgKind::Ident) => true,
        _ => false,
    }
}

/// Expand a `CompoundBody` into the property list it denotes.
///
/// `and` produces multiple `Property` values (the caller's `requires` list is
/// already a conjunction); `or` produces a single `Property::Or` property
/// whose `groups` encode the DNF groups.
fn expand_compound_body<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    body: &CompoundBody,
    exprs: &[Expr],
    params: &[String],
    param_tys: &[String],
) -> Vec<Property<'tcx>> {
    match body {
        CompoundBody::And(parts) => parts
            .iter()
            .flat_map(|p| expand_compound_body(tcx, def_id, p, exprs, params, param_tys))
            .collect(),
        CompoundBody::Or(parts) => {
            let mut disjuncts: Vec<Property<'tcx>> = Vec::new();
            for part in parts {
                let conjuncts = expand_compound_body(tcx, def_id, part, exprs, params, param_tys);
                if !conjuncts.is_empty() {
                    disjuncts.push(Property::conjunction(conjuncts));
                }
            }
            vec![Property::new_or(disjuncts)]
        }
        CompoundBody::Call { tag, args } => {
            // Validate the compound's parameter annotations against the primitive's
            // declared argument roles (e.g. a `Ptr` param used in a `Ty` slot).
            if let Some(spec) = super::spec::find_spec(tag) {
                match spec.build {
                    // Variadic target list (Alias/Alive): every param must be Ptr.
                    super::spec::BuildKind::Targets => {
                        for (pos, a) in args.iter().enumerate() {
                            if let CompoundArg::Param(i) = a
                                && let Some(def_ty) = param_tys.get(*i)
                                && !compound_param_ty_matches_arg_kind(
                                    def_ty,
                                    super::spec::ArgKind::Target,
                                )
                            {
                                let pname = params.get(*i).map(String::as_str).unwrap_or("?");
                                rap_warn!(
                                    "contract compound type mismatch: `{tag}` arg {pos} expects \
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
                                if let CompoundArg::Param(i) = a
                                    && let (Some(def_ty), Some(&arg_kind)) =
                                        (param_tys.get(*i), form.get(pos))
                                    && !compound_param_ty_matches_arg_kind(def_ty, arg_kind)
                                {
                                    let pname = params.get(*i).map(String::as_str).unwrap_or("?");
                                    rap_warn!(
                                        "contract compound type mismatch: `{tag}` arg {pos} expects \
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
                    CompoundArg::Param(i) => {
                        let Some(e) = exprs.get(*i) else {
                            return vec![unknown_property()];
                        };
                        resolved.push(e.clone());
                    }
                    CompoundArg::Lit(s) => {
                        let Ok(mut e) = syn::parse_str::<Expr>(s) else {
                            return vec![unknown_property()];
                        };
                        Subst { params, args: exprs }.visit_expr_mut(&mut e);
                        resolved.push(e);
                    }
                }
            }
            // Recurse through the normal property parser so nested compounds and
            // primitives are handled uniformly.
            Property::parse_list(tcx, def_id, tag, &resolved)
        }
    }
}

fn unknown_property<'tcx>() -> Property<'tcx> {
    Property::new_atom(PropertyKind::Unknown, Vec::new())
}

// ── Registry ───────────────────────────────────────────────────

/// Builtin compounds shipped with `rapx`: the standard compound safety properties
/// (`std-compound-properties.rs`) plus user extensions
/// (`user-compound-properties.rs`).  Immutable and shared across every crate.
fn builtin_compounds_map() -> &'static HashMap<String, CompoundSpec> {
    static BUILTIN: OnceLock<HashMap<String, CompoundSpec>> = OnceLock::new();
    BUILTIN.get_or_init(builtin_compounds)
}

/// Per-crate user compounds, registered from `#[rapx::def_property]` attributes.
///
/// Keyed by `CrateNum` so that compounds defined in one crate cannot leak into (or
/// collide with) another crate analyzed in the same process.  A crate's own
/// compounds shadow builtin compounds of the same name.
fn user_compounds_map() -> &'static RwLock<HashMap<CrateNum, HashMap<String, CompoundSpec>>> {
    static USER: OnceLock<RwLock<HashMap<CrateNum, HashMap<String, CompoundSpec>>>> = OnceLock::new();
    USER.get_or_init(|| RwLock::new(HashMap::new()))
}

/// Builtin compounds shipped with `rapx`: the standard compound safety properties
/// (`std-compound-properties.rs`) plus user extensions
/// (`user-compound-properties.rs`).
fn builtin_compounds() -> HashMap<String, CompoundSpec> {
    let mut map = HashMap::new();
    for compound in parse_compounds(include_str!("assets/std-compound-properties.rs")) {
        map.insert(compound.name.clone(), compound);
    }
    for compound in parse_compounds(include_str!("assets/user-compound-properties.rs")) {
        map.insert(compound.name.clone(), compound);
    }
    map
}

/// Look up a compound property by name, in the given crate's namespace first,
/// then the builtin namespace.
pub fn find_compound(krate: CrateNum, name: &str) -> Option<CompoundSpec> {
    if let Some(d) = user_compounds_map()
        .read()
        .ok()
        .and_then(|t| t.get(&krate).and_then(|m| m.get(name).cloned()))
    {
        return Some(d);
    }
    builtin_compounds_map().get(name).cloned()
}

/// Expand a named compound against concrete argument expressions.
pub fn expand_compound<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    name: &str,
    exprs: &[Expr],
) -> Option<Vec<Property<'tcx>>> {
    let compound = find_compound(def_id.krate, name)?;
    if compound.params.len() != exprs.len() {
        rap_warn!(
            "contract compound `{name}` expects {} argument(s), got {}",
            compound.params.len(),
            exprs.len()
        );
        return None;
    }
    // Guard against self-referential compounds (direct or mutual) before recursing;
    // otherwise `expand_compound_body` → `Property::parse_list` → `expand_compound` would
    // recurse forever and overflow the stack.
    if let Some(cycle) = find_compound_cycle(def_id.krate, name) {
        rap_error!("contract compound cycle detected: {}", cycle.join(" -> "));
        return None;
    }
    let mut props = expand_compound_body(tcx, def_id, &compound.body, exprs, &compound.params, &compound.param_tys);
    // Tag expanded properties with the compound name, its full call-site arguments,
    // and its doc-derived meaning so reports can show the compound as a single
    // entry instead of the underlying primitives.
    let arg_strings: Vec<String> = exprs
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let param_ty = compound.param_tys.get(i).map(|s| s.as_str()).unwrap_or("");
            resolve_arg_string(tcx, def_id, param_ty, e)
        })
        .collect();
    let meaning = if compound.doc.is_empty() {
        None
    } else {
        Some(compound.doc.join(" "))
    };
    for p in &mut props {
        p.set_origin(name.to_string(), arg_strings.clone(), meaning.clone());
    }
    Some(props)
}

/// Return a cycle path (e.g. `["A", "B", "A"]`) if expanding `start` can reach
/// itself again through compound-to-compound references, `None` otherwise.
///
/// Only edges that resolve to another registered compound are followed; calls to
/// primitives (`Allocated`, `Align`, ...) terminate the walk.  The crate's own
/// compounds are overlaid on the builtin namespace.
pub fn find_compound_cycle(krate: CrateNum, start: &str) -> Option<Vec<String>> {
    let mut combined = builtin_compounds_map().clone();
    if let Ok(user) = user_compounds_map().read()
        && let Some(crate_defs) = user.get(&krate)
    {
        for (name, compound) in crate_defs {
            combined.insert(name.clone(), compound.clone());
        }
    }
    find_cycle_in(start, &combined)
}

fn find_cycle_in(start: &str, table: &HashMap<String, CompoundSpec>) -> Option<Vec<String>> {
    fn dfs(
        name: &str,
        table: &HashMap<String, CompoundSpec>,
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
        let Some(compound) = table.get(name) else {
            return None;
        };
        path.push(name.to_string());
        for tag in compound_refs(&compound.body) {
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

/// Collect the tag names referenced by a `CompoundBody`, in left-to-right order.
fn compound_refs(body: &CompoundBody) -> Vec<String> {
    let mut out = Vec::new();
    collect_compound_refs(body, &mut out);
    out
}

fn collect_compound_refs(body: &CompoundBody, out: &mut Vec<String>) {
    match body {
        CompoundBody::And(parts) | CompoundBody::Or(parts) => {
            for part in parts {
                collect_compound_refs(part, out);
            }
        }
        CompoundBody::Call { tag, .. } => out.push(tag.clone()),
    }
}

// ── Registration of user-defined compounds ─────────────────────────

/// Parse compound-property declarations from `source` and insert them into the
/// given crate's namespace.  Returns the number of compounds registered.
pub fn register_compounds_from_source(krate: CrateNum, source: &str) -> usize {
    let compounds = parse_compounds(source);
    let n = compounds.len();
    if n == 0 {
        return 0;
    }
    let mut table = user_compounds_map().write().expect("compound table poisoned");
    let entry = table.entry(krate).or_default();
    for compound in compounds {
        entry.insert(compound.name.clone(), compound);
    }
    n
}

// ── Procedural-macro contract definitions ─────────────────────

/// Scan the local crate for `#[rapx::def_property("...")]` tool attributes
/// (emitted by the `rapx_macros::pred` proc-macro) and register each embedded
/// compound-property string.  Returns the number of compounds registered.
pub fn register_compound_properties(tcx: rustc_middle::ty::TyCtxt<'_>) -> usize {
    struct Visitor<'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        count: usize,
    }

    impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for Visitor<'tcx> {
        fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
            let attrs = self.tcx.hir_attrs(item.hir_id());
            for attr in attrs {
                if !is_def_property_attr(attr) {
                    continue;
                }
                let attr_str = crate::compat::attribute_to_string(self.tcx, attr);
                if let Some(def_str) = extract_def_property_string(&attr_str) {
                    let n = register_compounds_from_source(LOCAL_CRATE, &def_str);
                    if n > 0 {
                        rap_info!("rapx: registered {n} contract compound(s) from #[rapx::def_property]");
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

/// Whether an attribute path is `rapx::def_property` (or the bare form with the
/// tool prefix stripped).
fn is_def_property_attr(attr: &rustc_hir::Attribute) -> bool {
    let path = attr.path();
    if path.len() >= 2
        && path[path.len() - 2].as_str() == "rapx"
        && path[path.len() - 1].as_str() == "def_property"
    {
        return true;
    }
    path.len() == 1 && path[0].as_str() == "def_property"
}

/// Extract the string literal from a `#[rapx::def_property("compound ...")]`
/// attribute's textual representation.
fn extract_def_property_string(attr_str: &str) -> Option<String> {
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

