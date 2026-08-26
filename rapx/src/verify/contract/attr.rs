//! Parsing utilities for `#[rapx::requires(...)]` outer attributes.
//!
//! This module converts a raw `#[rapx::requires(...)]` attribute string into a
//! structured representation that the verification analysis can consume without
//! depending on `syn` expression details in later stages.
//!
//! The currently supported shape is:
//!
//! ```text
//! #[rapx::requires(property_call, kind = "...")]
//! ```
//!
//! where `kind = "..."` applies to the property in the same attribute.

use syn::{
    Expr, Lit, Result as SynResult, Token,
    parse::{Parse, ParseStream},
};

use quote::ToTokens;

use regex::Regex;
use std::sync::LazyLock;

/// The raw syntactic form of a property call `tag(arg0, arg1, ...)` parsed
/// from an attribute — the *unevaluated* stage, before semantic resolution
/// into a [`Property`](crate::verify::contract::Property).
#[derive(Debug, Clone)]
pub struct PropertyCall {
    /// The property name extracted from the call target.
    pub tag: String,
    /// The positional arguments passed to the property call.
    pub args: Vec<Expr>,
    /// Optional `kind` metadata associated with this property.
    pub kind: Option<String>,
}

impl Parse for PropertyCall {
    /// Parse a single property item from a `requires` attribute argument list.
    ///
    /// Supported forms:
    /// - `nonzero(x)`
    /// - `nonzero(x), kind = "ptr"`
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

/// A thin wrapper that allows parsing exactly one outer attribute from a string.
struct RequireOuterAttribute {
    attr: syn::Attribute,
}

impl Parse for RequireOuterAttribute {
    /// Parse exactly one outer attribute.
    fn parse(input: ParseStream<'_>) -> SynResult<Self> {
        Ok(Self {
            attr: input
                .call(syn::Attribute::parse_outer)?
                .into_iter()
                .next()
                .ok_or_else(|| input.error("expected exactly one outer attribute"))?,
        })
    }
}

/// Parse a raw attribute string into a structured `requires` property.
///
/// Returns `Ok(None)` when the attribute does not match `rapx::<expected_name>`
/// or when it is not a list attribute.
pub fn parse_rapx_attr(
    attr_str: &str,
    expected_name: &str,
) -> SynResult<Option<PropertyCall>> {
    let attr_str = strip_lifetime_ticks(attr_str);
    // Parse the raw string into a single outer attribute node.
    let attr = syn::parse_str::<RequireOuterAttribute>(&attr_str)?.attr;
    if !is_expected_syn_rapx_attr(&attr, expected_name) {
        return Ok(None);
    }

    // Only list-style attributes carry an argument list.
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Ok(None);
    };

    let property = meta_list.parse_args::<PropertyCall>()?;
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
fn parse_property_head(input: ParseStream<'_>) -> SynResult<PropertyCall> {
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

    Ok(PropertyCall {
        tag,
        args,
        kind: None,
    })
}

/// Parse a single property argument as an `Expr`.
///
/// Generic type arguments (`Option<NonZero<T>>`, `NonZero<T>`) cannot be parsed
/// as an expression — `syn` would read `<`/`>` as comparison operators — so on
/// failure we fall back to parsing the argument as a `syn::Type` and wrap its
/// token stream as `Expr::Verbatim`.
fn parse_property_arg(input: ParseStream<'_>) -> SynResult<Expr> {
    let fork = input.fork();
    if fork.parse::<Expr>().is_ok() {
        return input.parse::<Expr>();
    }
    let ty: syn::Type = input.parse()?;
    Ok(Expr::Verbatim(ty.to_token_stream()))
}

/// Strips the leading `'` from Rust lifetime tokens so that `syn` can
/// parse them as regular identifier expressions inside attribute arguments.
/// For example, `'a` becomes `a`, `'static` becomes `static`.
static LIFETIME_TICK_RE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"'([a-zA-Z_][a-zA-Z0-9_]*)").unwrap());

fn strip_lifetime_ticks(s: &str) -> String {
    LIFETIME_TICK_RE.replace_all(s, "$1").to_string()
}
