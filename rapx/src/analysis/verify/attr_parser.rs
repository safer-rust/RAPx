use syn::{
    Attribute, Expr, ExprCall, ExprPath, Lit, Result as SynResult, Token,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

#[derive(Debug, Clone)]
pub struct ParsedProperty {
    pub tag: String,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone, Default)]
pub struct ParsedRapxAttr {
    pub kind: Option<String>,
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
                if let Expr::Lit(expr_lit) = value
                    && let Lit::Str(kind) = expr_lit.lit
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

pub fn parse_rapx_attr(attr_str: &str, expected_name: &str) -> SynResult<ParsedRapxAttr> {
    let attr = syn::parse_str::<Attribute>(attr_str)?;
    if !is_expected_syn_rapx_attr(&attr, expected_name) {
        return Ok(ParsedRapxAttr::default());
    }

    let mut parsed = ParsedRapxAttr::default();
    let items = match &attr.meta {
        syn::Meta::List(meta_list) => {
            meta_list.parse_args_with(Punctuated::<RapxAttrItem, Token![,]>::parse_terminated)?
        }
        _ => return Ok(parsed),
    };

    for item in items {
        match item {
            RapxAttrItem::Property(property) => parsed.properties.push(property),
            RapxAttrItem::Kind(kind) => parsed.kind = Some(kind),
        }
    }

    Ok(parsed)
}

fn is_expected_syn_rapx_attr(attr: &Attribute, expected_name: &str) -> bool {
    let segments: Vec<_> = attr
        .path()
        .segments
        .iter()
        .map(|seg| seg.ident.to_string())
        .collect();

    segments.len() == 2 && segments[0] == "rapx" && segments[1] == expected_name
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
            })
        }
        other => Err(syn::Error::new_spanned(
            other,
            "unsupported RAPx property expression",
        )),
    }
}
