use syn::{
    Expr, ExprCall, ExprPath, Lit, Result as SynResult, Token,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

#[derive(Debug, Clone)]
pub struct ParsedProperty {
    pub tag: String,
    pub args: Vec<Expr>,
    pub kind: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub struct ParsedRapxAttr {
    pub properties: Vec<ParsedProperty>,
}

enum RapxAttrItem {
    Property(ParsedProperty),
    Kind(String),
}

impl Parse for RapxAttrItem {
    fn parse(input: ParseStream<'_>) -> SynResult<Self> {
        if input.peek(syn::Ident) && input.peek2(Token![=]) {
            let ident: syn::Ident = input.parse()?;
            let _: Token![=] = input.parse()?;
            let value: Expr = input.parse()?;

            if ident == "kind" {
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

            return Err(syn::Error::new(
                ident.span(),
                "unsupported named RAPx attribute argument",
            ));
        }

        let expr: Expr = input.parse()?;
        Ok(Self::Property(parse_property_expr(expr)?))
    }
}

struct RapxOuterAttribute {
    attr: syn::Attribute,
}

impl Parse for RapxOuterAttribute {
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

pub fn parse_rapx_attr(attr_str: &str, expected_name: &str) -> SynResult<ParsedRapxAttr> {
    let attr = syn::parse_str::<RapxOuterAttribute>(attr_str)?.attr;
    if !is_expected_syn_rapx_attr(&attr, expected_name) {
        return Ok(ParsedRapxAttr::default());
    }

    let syn::Meta::List(meta_list) = &attr.meta else {
        return Ok(ParsedRapxAttr::default());
    };

    let items =
        meta_list.parse_args_with(Punctuated::<RapxAttrItem, Token![,]>::parse_terminated)?;

    let mut parsed = ParsedRapxAttr::default();
    for item in items {
        match item {
            RapxAttrItem::Property(property) => parsed.properties.push(property),
            RapxAttrItem::Kind(kind) => {
                let last = parsed.properties.last_mut().ok_or_else(|| {
                    syn::Error::new_spanned(&attr, "kind must follow a RAPx property")
                })?;

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

fn is_expected_syn_rapx_attr(attr: &syn::Attribute, expected_name: &str) -> bool {
    let mut segments = attr.path().segments.iter();
    matches!(
        (segments.next(), segments.next(), segments.next()),
        (Some(first), Some(second), None)
            if first.ident == "rapx" && second.ident == expected_name
    )
}

fn parse_property_expr(expr: Expr) -> SynResult<ParsedProperty> {
    match expr {
        Expr::Call(ExprCall { func, args, .. }) => {
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
