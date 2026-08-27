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
    Expr, Lit, Result as SynResult, Token, Type,
    parse::{Parse, ParseStream},
};

use quote::ToTokens;

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
pub(crate) fn parse_rapx_attr(
    attr_str: &str,
    expected_name: &str,
) -> SynResult<Option<AttrProperty>> {
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
                let char_literal = match chars.get(i + 1) {
                    Some('\\') => chars.get(i + 3) == Some(&'\''),
                    Some(_) => chars.get(i + 2) == Some(&'\''),
                    None => false,
                };
                if char_literal {
                    out.push('\'');
                }
                i += 1;
            }
            c => {
                out.push(c);
                i += 1;
            }
        }
    }
    out
}
