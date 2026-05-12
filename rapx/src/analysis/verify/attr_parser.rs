//! Parsing utilities for `#[rapx::<name>(...)]` outer attributes.
//!
//! This module converts a raw attribute string (as it appears in Rust source
//! code) into a structured [`ParsedRapxAttr`] value that the rest of the
//! analysis pipeline can inspect without touching `syn` internals.
//!
//! # Attribute grammar
//!
//! ```text
//! #[rapx::<name>( [item ,]* )]
//!
//! item  ::= property_call
//!         | "kind" "=" string_literal
//!
//! property_call ::= ident "(" [expr ,]* ")"
//! ```
//!
//! # Example
//!
//! Given the attribute string `#[rapx::verify(nonzero(x), kind = "safety")]`,
//! [`parse_rapx_attr`] will return a [`ParsedRapxAttr`] where:
//!
//! - `properties[0].tag`  == `"nonzero"`
//! - `properties[0].args` == `[x]`
//! - `properties[0].kind` == `Some("safety")`

use syn::{
    Expr, ExprCall, ExprPath, Lit, Result as SynResult, Token,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

/// A single property extracted from a `#[rapx::<name>(...)]` attribute.
///
/// Properties have the call-expression form `tag(arg0, arg1, …)`.  An
/// optional `kind` string can follow immediately after the property in the
/// attribute argument list as a named `kind = "…"` argument.
#[derive(Debug, Clone)]
pub struct ParsedProperty {
    /// The name of the property (the callee identifier, e.g. `"nonzero"`).
    pub tag: String,
    /// The positional arguments passed to the property call.
    pub args: Vec<Expr>,
    /// An optional qualifier that refines the property (e.g. `"safety"`).
    ///
    /// Set by a `kind = "<value>"` token that immediately follows this
    /// property in the attribute argument list.
    pub kind: Option<String>,
}

/// The fully-parsed representation of a single `#[rapx::<name>(...)]` attribute.
///
/// If the attribute string does not match the expected name, or if it does not
/// use list-style meta syntax, the default (empty) value is returned instead of
/// an error.
#[derive(Debug, Clone, Default)]
pub struct ParsedRapxAttr {
    /// All properties found in the attribute argument list, in source order.
    pub properties: Vec<ParsedProperty>,
}

/// An intermediate item parsed from one comma-separated slot in the attribute
/// argument list.
///
/// - [`Property`](RapxAttrItem::Property) – a bare call expression such as
///   `nonzero(x)`.
/// - [`Kind`](RapxAttrItem::Kind) – a named argument of the form
///   `kind = "some_string"` that is attached to the preceding property.
enum RapxAttrItem {
    /// A call-style property expression (e.g. `nonzero(x, y)`).
    Property(ParsedProperty),
    /// A `kind = "<value>"` named argument that qualifies the preceding property.
    Kind(String),
}

impl Parse for RapxAttrItem {
    /// Parse one comma-separated item from the RAPx attribute argument list.
    ///
    /// Two forms are accepted:
    ///
    /// 1. `ident = expr` – currently only `kind = "<string>"` is valid.
    /// 2. A bare expression, which must be a call expression and is forwarded
    ///    to [`parse_property_expr`].
    ///
    /// Any other named argument or non-call bare expression is rejected with a
    /// descriptive [`syn::Error`].
    fn parse(input: ParseStream<'_>) -> SynResult<Self> {
        // Check for the named-argument form `ident = expr`.
        if input.peek(syn::Ident) && input.peek2(Token![=]) {
            let ident: syn::Ident = input.parse()?;
            let _: Token![=] = input.parse()?;
            let value: Expr = input.parse()?;

            if ident == "kind" {
                // `kind` must be assigned a plain string literal.
                if let Expr::Lit(ref expr_lit) = value
                    && let Lit::Str(ref kind) = expr_lit.lit
                {
                    return Ok(Self::Kind(kind.value()));
                }

                return Err(syn::Error::new_spanned(
                    value,
                    "RAPx attribute kind must be a string literal",
                ));
            }

            // No other named arguments are recognised.
            return Err(syn::Error::new(
                ident.span(),
                "unsupported named RAPx attribute argument",
            ));
        }

        // Otherwise parse a bare expression and expect a call-expression form.
        let expr: Expr = input.parse()?;
        Ok(Self::Property(parse_property_expr(expr)?))
    }
}

/// A thin newtype wrapper around [`syn::Attribute`] that implements [`Parse`].
///
/// `syn` does not implement `Parse` for `syn::Attribute` directly when used
/// with [`syn::parse_str`].  This wrapper calls
/// [`Attribute::parse_outer`](syn::Attribute::parse_outer) and extracts the
/// first (and only expected) attribute from the result.
struct RapxOuterAttribute {
    attr: syn::Attribute,
}

impl Parse for RapxOuterAttribute {
    /// Parse exactly one outer attribute (e.g. `#[rapx::verify(...)]`).
    ///
    /// Returns an error if the input contains no outer attributes.
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

/// Parse a raw attribute string into a [`ParsedRapxAttr`].
///
/// # Parameters
///
/// - `attr_str`      – The raw source text of the attribute, e.g.
///   `"#[rapx::verify(nonzero(x), kind = \"safety\")]"`.
/// - `expected_name` – The second path segment that the attribute must have
///   (e.g. `"verify"`).  If the attribute path does not match
///   `rapx::<expected_name>`, an empty default is returned.
///
/// # Returns
///
/// - `Ok(parsed)` – The attribute matched and was parsed successfully.
/// - `Ok(default)` – The attribute did not match `expected_name`, or it used
///   non-list meta syntax (e.g. `#[rapx::verify]` without parentheses).
/// - `Err(e)` – The attribute string could not be tokenised, or its argument
///   list contained an invalid item.
pub fn parse_rapx_attr(attr_str: &str, expected_name: &str) -> SynResult<ParsedRapxAttr> {
    // Parse the raw string as a single outer attribute.
    let attr = syn::parse_str::<RapxOuterAttribute>(attr_str)?.attr;

    // Silently ignore attributes that do not match `rapx::<expected_name>`.
    if !is_expected_syn_rapx_attr(&attr, expected_name) {
        return Ok(ParsedRapxAttr::default());
    }

    // Only list-style meta (`#[rapx::name(...)]`) carries arguments.
    let syn::Meta::List(meta_list) = &attr.meta else {
        return Ok(ParsedRapxAttr::default());
    };

    // Parse the comma-separated argument list into a sequence of `RapxAttrItem`s.
    let items =
        meta_list.parse_args_with(Punctuated::<RapxAttrItem, Token![,]>::parse_terminated)?;

    // Distribute each item into the appropriate field of `ParsedRapxAttr`.
    let mut parsed = ParsedRapxAttr::default();
    for item in items {
        match item {
            // A call-style property: push it onto the list.
            RapxAttrItem::Property(property) => parsed.properties.push(property),
            // A `kind = "…"` argument: attach it to the most recent property.
            RapxAttrItem::Kind(kind) => {
                let last = parsed.properties.last_mut().ok_or_else(|| {
                    syn::Error::new_spanned(&attr, "kind must follow a RAPx property")
                })?;

                // Reject duplicate `kind` assignments for the same property.
                if last.kind.is_some() {
                    return Err(syn::Error::new_spanned(
                        &attr,
                        "duplicate kind for RAPx property",
                    ));
                }

                last.kind = Some(kind);
            }
        }
    }

    Ok(parsed)
}

/// Return `true` if `attr` has exactly the two-segment path `rapx::<expected_name>`.
///
/// Attributes with additional path segments (e.g. `rapx::foo::bar`) or with
/// only one segment are rejected.
fn is_expected_syn_rapx_attr(attr: &syn::Attribute, expected_name: &str) -> bool {
    let mut segments = attr.path().segments.iter();
    matches!(
        (segments.next(), segments.next(), segments.next()),
        (Some(first), Some(second), None)
            if first.ident == "rapx" && second.ident == expected_name
    )
}

/// Convert an [`Expr`] into a [`ParsedProperty`].
///
/// The expression must be a function-call form (`tag(arg0, arg1, …)`) where
/// the callee is a simple path expression.  The last path segment becomes the
/// property [`tag`](ParsedProperty::tag).
///
/// # Errors
///
/// Returns a [`syn::Error`] if:
/// - The expression is not a call expression.
/// - The callee is not a path expression (e.g. a closure or method call).
/// - The callee path has no segments (should be unreachable in practice).
fn parse_property_expr(expr: Expr) -> SynResult<ParsedProperty> {
    match expr {
        Expr::Call(ExprCall { func, args, .. }) => {
            // Extract the property name from the last segment of the callee path.
            let tag = match *func {
                Expr::Path(ExprPath { path, .. }) => path
                    .segments
                    .last()
                    .map(|seg| seg.ident.to_string())
                    .ok_or_else(|| syn::Error::new_spanned(path, "missing property name"))?,
                other => {
                    // Callee is not a plain path (e.g. it is a closure or an index expression).
                    return Err(syn::Error::new_spanned(
                        other,
                        "unsupported RAPx property callee expression",
                    ));
                }
            };

            Ok(ParsedProperty {
                tag,
                args: args.into_iter().collect(),
                // `kind` is filled in later from a subsequent `kind = "…"` item.
                kind: None,
            })
        }
        // Only call expressions are valid property forms.
        other => Err(syn::Error::new_spanned(
            other,
            "unsupported RAPx property expression",
        )),
    }
}
