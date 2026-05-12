//! Parsing utilities for `#[rapx::requires(...)]` outer attributes.
//!
//! This module converts a raw `#[rapx::requires(...)]` attribute string into a
//! structured representation that the verification analysis can consume without
//! depending on `syn` expression details in later stages.
//!
//! The currently supported shape is:
//!
//! ```text
//! #[rapx::requires(property_call; kind = "...")]
//! ```
//!
//! where `kind = "..."` applies to the property in the same item.

use syn::{
    Expr, ExprCall, ExprPath, Lit, Result as SynResult, Token,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

/// A parsed `requires` property in the form `tag(arg0, arg1, ...)`.
#[derive(Debug, Clone)]
pub struct ParsedProperty {
    /// The property name extracted from the call target.
    pub tag: String,
    /// The positional arguments passed to the property call.
    pub args: Vec<Expr>,
    /// Optional `kind` metadata associated with this property.
    pub kind: Option<String>,
}

/// The parsed result of a `#[rapx::requires(...)]` attribute.
#[derive(Debug, Clone, Default)]
pub struct ParsedRapxAttr {
    /// All parsed properties in source order.
    pub properties: Vec<ParsedProperty>,
}

/// One property item inside `#[rapx::requires(...)]`.
///
/// Supported forms:
/// - `nonzero(x)`
/// - `nonzero(x); kind = "ptr"`
impl Parse for ParsedProperty {
    /// Parse one property item from a `requires` attribute argument list.
    fn parse(input: ParseStream<'_>) -> SynResult<Self> {
        let expr: Expr = input.parse()?;
        let mut property = parse_property_expr(expr)?;

        if input.peek(Token![;]) {
            let _: Token![;] = input.parse()?;

            while !input.is_empty() && !input.peek(Token![,]) {
                let ident: syn::Ident = input.parse()?;
                let _: Token![=] = input.parse()?;
                let value: Expr = input.parse()?;

                match ident.to_string().as_str() {
                    "kind" => {
                        if property.kind.is_some() {
                            return Err(syn::Error::new(
                                ident.span(),
                                "duplicate kind for RAPx property",
                            ));
                        }

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
                    }
                    _ => {
                        return Err(syn::Error::new(
                            ident.span(),
                            "unsupported named RAPx requires attribute argument",
                        ));
                    }
                }

                if input.peek(Token![,]) {
                    break;
                }

                let _: Token![;] = input.parse()?;
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

/// Parse a raw attribute string into a structured `requires` representation.
///
/// Returns an empty default value when the attribute does not match
/// `rapx::requires` or when it is not a list attribute.
pub fn parse_rapx_attr(attr_str: &str, expected_name: &str) -> SynResult<ParsedRapxAttr> {
    // Parse the raw string into a single outer attribute node.
    let attr = syn::parse_str::<RequireOuterAttribute>(attr_str)?.attr;
    if !is_expected_syn_rapx_attr(&attr, expected_name) {
        return Ok(ParsedRapxAttr::default());
    }

    // Only list-style attributes carry a comma-separated argument list.
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Ok(ParsedRapxAttr::default());
    };

    let properties =
        meta_list.parse_args_with(Punctuated::<ParsedProperty, Token![,]>::parse_terminated)?;

    Ok(ParsedRapxAttr {
        properties: properties.into_iter().collect(),
    })
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

/// Parse a property call expression into a [`ParsedProperty`].
fn parse_property_expr(expr: Expr) -> SynResult<ParsedProperty> {
    match expr {
        Expr::Call(ExprCall { func, args, .. }) => {
            // Use the final segment of the callee path as the property tag.
            let tag = match *func {
                Expr::Path(ExprPath { path, .. }) => path
                    .segments
                    .last()
                    .map(|seg| seg.ident.to_string())
                    .ok_or_else(|| syn::Error::new_spanned(path, "missing property name"))?,
                other => {
                    return Err(syn::Error::new_spanned(
                        other,
                        "unsupported RAPx property callee expression",
                    ));
                }
            };

            Ok(ParsedProperty {
                tag,
                args: args.into_iter().collect(),
                kind: None,
            })
        }
        other => Err(syn::Error::new_spanned(
            other,
            "unsupported RAPx property expression",
        )),
    }
}
