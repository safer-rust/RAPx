//! Parsing utilities for RAPx contract attributes.
//!
//! Parses raw `#[rapx::<name>(...)]` attributes (`requires` / `invariant` /
//! `ensures`) and resolves their properties for verification.
//!
//! The supported shape is:
//!
//! ```text
//! #[rapx::<name>(property_call, kind = "...")]
//! ```
//!
//! where `kind = "..."` (a string literal) applies to the property in the same
//! attribute.

use syn::{
    Expr, Lit, Result as SynResult, Token, Type,
    parse::{Parse, ParseStream},
};

use quote::ToTokens;

#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::Attribute;
#[cfg(not(rapx_has_attr_ir))]
use rustc_hir::Attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

use super::Property;

/// The raw syntactic form of a property call `tag(arg0, arg1, ...)` parsed
/// from an attribute — the *unevaluated* stage, before semantic resolution
/// into a [`Property`](crate::verify::contract::Property).
#[derive(Debug, Clone)]
pub(crate) struct AttrProperty {
    /// The property name extracted from the call target.
    pub tag: String,
    /// The positional arguments passed to the property call.
    pub args: Vec<Expr>,
    /// Optional `kind` metadata associated with this property.
    pub kind: Option<String>,
}

impl Parse for AttrProperty {
    /// Parse a single property item from an attribute argument list.
    ///
    /// Supported forms:
    /// - `NonNull(x)`
    /// - `NonNull(x), kind = "precond"`
    fn parse(input: ParseStream<'_>) -> SynResult<Self> {
        let mut property = parse_property_head(input)?;

        if input.peek(Token![,]) {
            let fork = input.fork();
            let _: Token![,] = fork.parse()?;
            if fork.peek(syn::Ident) && fork.peek2(Token![=]) {
                let _: Token![,] = input.parse()?;
                let ident: syn::Ident = input.parse()?;
                let _: Token![=] = input.parse()?;
                let value: Expr = input.parse()?;

                if ident == "kind" {
                    if let Expr::Lit(ref expr_lit) = value
                        && let Lit::Str(ref kind) = expr_lit.lit
                    {
                        property.kind = Some(kind.value());
                    } else {
                        return Err(syn::Error::new_spanned(
                            value,
                            "RAPx requires attribute kind must be a string literal",
                        ));
                    }
                } else {
                    return Err(syn::Error::new(
                        ident.span(),
                        "unsupported named RAPx requires attribute argument",
                    ));
                }
            }
        }

        Ok(property)
    }
}

pub(crate) fn parse_outer_attr(input: ParseStream<'_>) -> SynResult<syn::Attribute> {
    input
        .call(syn::Attribute::parse_outer)?
        .into_iter()
        .next()
        .ok_or_else(|| input.error("expected an outer attribute"))
}

/// Parse a raw attribute string into a structured `requires` property.
///
/// Returns `Ok(None)` when the attribute does not match `rapx::<expected_name>`
/// or when it is not a list attribute.
pub(crate) fn parse_rapx_attr(
    attr_str: &str,
    expected_name: &str,
) -> SynResult<Option<AttrProperty>> {
    let attr_str = strip_lifetime_ticks(attr_str);
    let attr = syn::parse::Parser::parse_str(parse_outer_attr, &attr_str)?;
    if !is_expected_syn_rapx_attr(&attr, expected_name) {
        return Ok(None);
    }

    let syn::Meta::List(meta_list) = &attr.meta else {
        return Ok(None);
    };

    let property = meta_list.parse_args::<AttrProperty>()?;
    Ok(Some(property))
}

/// Check whether an attribute path is exactly `rapx::<expected_name>`.
fn is_expected_syn_rapx_attr(attr: &syn::Attribute, expected_name: &str) -> bool {
    let mut segments = attr.path().segments.iter();
    matches!(
        (segments.next(), segments.next(), segments.next()),
        (Some(first), Some(second), None)
            if first.ident == "rapx" && second.ident == expected_name
    )
}

/// Parse a property call head `tag(arg0, arg1, ...)`.
///
/// The argument list is parsed position-by-position rather than as a single
/// `Expr::Call`, because property arguments may be generic *types* (e.g.
/// `ValidTransmute(T, Option<NonZero<T>>)`) that `syn` cannot parse as value
/// expressions.
fn parse_property_head(input: ParseStream<'_>) -> SynResult<AttrProperty> {
    let path: syn::Path = input.parse()?;
    let tag = path
        .segments
        .last()
        .map(|seg| seg.ident.to_string())
        .ok_or_else(|| syn::Error::new_spanned(&path, "missing property name"))?;

    let content;
    syn::parenthesized!(content in input);

    let mut args: Vec<Expr> = Vec::new();
    while !content.is_empty() {
        args.push(parse_property_arg(&content)?);
        if content.is_empty() {
            break;
        }
        content.parse::<Token![,]>()?;
    }

    Ok(AttrProperty {
        tag,
        args,
        kind: None,
    })
}

/// Parse a single property argument as an `Expr`.
///
/// Arguments are usually types (`Option<NonZero<T>>`, `[T; N]`, `T`), which
/// `syn` cannot parse as value expressions (it would read `<`/`>` as comparison
/// operators), so we try `Type` first and wrap its token stream as
/// `Expr::Verbatim`.  Plain path types (single- or multi-segment identifiers
/// without generics) are kept as `Expr::Path` so downstream place/ident
/// resolution still recognises them.  Arguments that are genuine expressions
/// (`0`, `x + 1`, `ptr.0`) fail type parsing and fall back to `Expr`.
fn parse_property_arg(input: ParseStream<'_>) -> SynResult<Expr> {
    // Arguments that begin with a parenthesised group are tuple/parenthesised
    // expressions (e.g. the disjunctive grouping `(Align(head, T), ValidPtr(...))`
    // inside `any`), never types.  syn's `Type` parser is fooled by these: it
    // parses `(Align(head, T))` as a `Type::Paren` around just `Align` and
    // silently leaves the rest of the group unparsed, which then surfaces as a
    // spurious `unexpected token, expected `)`` error.  Parse them directly as
    // expressions instead.
    if input.peek(syn::token::Paren) {
        return input.parse::<Expr>();
    }

    let fork = input.fork();
    if fork.parse::<Type>().is_ok() && (fork.is_empty() || fork.peek(Token![,])) {
        let ty: Type = input.parse()?;
        return Ok(type_to_arg_expr(ty));
    }
    input.parse::<Expr>()
}

/// Convert a parsed argument `Type` back into the `Expr` form expected by the
/// property builder: plain paths stay `Expr::Path`, everything else (generics,
/// arrays, tuples, references) becomes `Expr::Verbatim`.
fn type_to_arg_expr(ty: Type) -> Expr {
    if let Type::Path(type_path) = &ty
        && type_path.qself.is_none()
        && type_path
            .path
            .segments
            .iter()
            .all(|s| matches!(s.arguments, syn::PathArguments::None))
    {
        return Expr::Path(syn::ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: type_path.path.clone(),
        });
    }
    Expr::Verbatim(ty.to_token_stream())
}

/// Strips the leading `'` from Rust lifetime tokens so that `syn` can
/// parse them as regular identifier expressions inside attribute arguments.
/// For example, `'a` becomes `a`, `'static` becomes `static`.
///
/// String literals (`"..."`) and char literals (`'x'`) are copied verbatim so
/// their contents are never altered.
fn strip_lifetime_ticks(s: &str) -> String {
    let chars: Vec<char> = s.chars().collect();
    let mut out = String::with_capacity(s.len());
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            '"' => {
                out.push('"');
                i += 1;
                while i < chars.len() {
                    let c = chars[i];
                    out.push(c);
                    i += 1;
                    if c == '\\' && i < chars.len() {
                        out.push(chars[i]);
                        i += 1;
                    } else if c == '"' {
                        break;
                    }
                }
            }
            '\'' => {
                // `'static` is a Rust keyword, so it cannot be parsed as a
                // plain ident after the tick is stripped. Map it to a
                // non-keyword token that `resolve_region_name` recognises.
                let rest: String = chars[i + 1..].iter().collect();
                if rest.starts_with("static")
                    && chars.get(i + 1 + "static".len()).is_none_or(|&c| !c.is_ascii_alphanumeric() && c != '_')
                {
                    out.push_str(super::STATIC_LIFETIME_IDENT);
                    i += 1 + "static".len();
                    continue;
                }
                let len = match chars.get(i + 1) {
                    Some('\\') if chars.get(i + 3) == Some(&'\'') => 4,
                    Some(_) if chars.get(i + 2) == Some(&'\'') => 3,
                    _ => 0,
                };
                if len > 0 {
                    out.extend(&chars[i..i + len]);
                    i += len;
                } else {
                    i += 1;
                }
            }
            c => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}

pub(crate) fn is_rapx_named_attr(tcx: TyCtxt<'_>, attr: &Attribute, name: &str) -> bool {
    let name = Symbol::intern(name);
    crate::compat::attribute_path_matches(tcx, attr, &[Symbol::intern("rapx"), name])
        || crate::compat::attribute_path_matches(tcx, attr, &[name])
}

pub(crate) fn collect_properties_from_named_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
    attr_name: &str,
) -> Vec<Property<'tcx>> {
    let mut results = Vec::new();

    for attr in attrs {
        if !is_rapx_named_attr(tcx, attr, attr_name) {
            continue;
        }

        let attr_str = crate::compat::attribute_to_string(tcx, attr);
        let parsed = match parse_rapx_attr(attr_str.as_str(), attr_name) {
            Ok(parsed) => parsed,
            Err(err) => {
                rap_error!(
                    "Failed to parse RAPx {} attr '{}': {}",
                    parse_error_label,
                    attr_str,
                    err
                );
                continue;
            }
        };

        let Some(property) = parsed else { continue };
        results.extend(
            Property::parse_list(tcx, property_def_id, property.tag.as_str(), &property.args)
                .into_iter()
                .map(move |mut p| {
                    p.apply_kind(property.kind.as_deref());
                    p
                }),
        );
    }

    results
}
