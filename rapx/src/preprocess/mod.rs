pub mod dummy_fns;
pub mod ssa_preprocess;

use rustc_ast::{
    token::{CommentKind, Delimiter, Lit, Token, TokenKind},
    tokenstream::{DelimSpan, Spacing, TokenStream, TokenTree},
    *,
};
use rustc_span::{DUMMY_SP, Ident, symbol::Symbol};
use thin_vec::ThinVec;

/// Empty `#[doc]` on the struct.
/// cc https://github.com/Artisan-Lab/RAPx/issues/184
fn doc_attr() -> Attribute {
    Attribute {
        kind: AttrKind::DocComment(CommentKind::Line, Symbol::intern("doc")),
        id: AttrId::ZERO,
        style: AttrStyle::Outer,
        span: DUMMY_SP,
    }
}

// #[stable(feature = "foo", since = "1.93")]
fn stability_attr() -> Attribute {
    let mut attr = NormalAttr::from_ident(Ident::from_str("stable"));
    let tokens: Vec<_> = {
        let feature = Token::from_ast_ident(Ident::from_str("feature"));
        let eq = Token::new(TokenKind::Eq, DUMMY_SP);
        let feature_val = Token::new(
            TokenKind::Literal(Lit::new(token::LitKind::Str, Symbol::intern("foo"), None)),
            DUMMY_SP,
        );
        let comma = Token::new(TokenKind::Comma, DUMMY_SP);
        let since = Token::from_ast_ident(Ident::from_str("since"));
        let since_val = Token::new(
            TokenKind::Literal(Lit::new(token::LitKind::Str, Symbol::intern("1.93"), None)),
            DUMMY_SP,
        );
        [feature, eq, feature_val, comma, since, eq, since_val]
            .into_iter()
            .map(|t| TokenTree::Token(t, Spacing::Alone))
            .collect()
    };
    let delim_args = DelimArgs {
        dspan: DelimSpan::dummy(),
        delim: Delimiter::Parenthesis,
        tokens: TokenStream::new(tokens),
    };
    #[cfg(rapx_rustc_ge_100)]
    {
        attr.item.args = rustc_ast::MetaItemKind::Unparsed(AttrArgs::Delimited(delim_args));
    }
    #[cfg(all(rapx_rustc_ge_196, not(rapx_rustc_ge_100)))]
    {
        attr.item.args = rustc_ast::AttrItemKind::Unparsed(AttrArgs::Delimited(delim_args));
    }
    #[cfg(not(rapx_rustc_ge_196))]
    {
        attr.item.args = AttrArgs::Delimited(delim_args);
    }
    Attribute {
        kind: AttrKind::Normal(attr.into()),
        id: AttrId::ZERO,
        style: AttrStyle::Outer,
        span: DUMMY_SP,
    }
}

fn set_attrs(build_std: bool) -> ThinVec<Attribute> {
    let mut v = ThinVec::with_capacity(2);
    v.push(doc_attr());
    if build_std {
        v.push(stability_attr());
    }
    v
}
