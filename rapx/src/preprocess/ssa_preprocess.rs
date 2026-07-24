use super::set_attrs;
#[cfg(rapx_rustc_ge_198)]
use rustc_ast::MutRestriction;
#[cfg(rapx_rustc_ge_198)]
use rustc_ast::RestrictionKind;
use rustc_ast::*;
use rustc_span::{
    DUMMY_SP,
    symbol::{Ident, Symbol},
};
use thin_vec::ThinVec;

pub(crate) fn create_ssa_struct(_krate: &mut Crate, build_std: bool) {
    rap_debug!("[CALLBACK] Injecting new structs into the AST...");

    let ssa_struct = create_struct(
        "SSAstmt",
        vec![
            ("para1", Symbol::intern("i128")),
            ("para2", Symbol::intern("i128")),
            ("para3", Symbol::intern("i128")),
            ("para4", Symbol::intern("i128")),
            ("para5", Symbol::intern("i128")),
            ("para6", Symbol::intern("i128")),
            ("para7", Symbol::intern("i128")),
            ("para8", Symbol::intern("i128")),
            ("para9", Symbol::intern("i128")),
            ("para10", Symbol::intern("i128")),
        ],
        build_std,
    );

    let essa_struct = create_struct(
        "ESSAstmt",
        vec![
            ("op1", Symbol::intern("i128")),
            ("op2", Symbol::intern("i128")),
            ("cmp", Symbol::intern("i128")),
            ("switch_bb", Symbol::intern("i128")),
        ],
        build_std,
    );

    _krate.items.push(ssa_struct);
    _krate.items.push(essa_struct);

    // println!("[CALLBACK] Injection complete. Continuing compilation...");
}
pub(crate) fn create_struct(
    name: &str,
    fields_def: Vec<(&str, Symbol)>,
    build_std: bool,
) -> Box<Item> {
    let fields: ThinVec<FieldDef> = fields_def
        .into_iter()
        .map(|(fname, fty)| {
            #[cfg(rapx_has_fielddef_extras)]
            {
                FieldDef {
                    attrs: set_attrs(build_std),
                    vis: Visibility {
                        span: DUMMY_SP,
                        kind: VisibilityKind::Public,
                    },
                    extras: Some(Box::new(FieldDefExtras {
                        safety: Safety::Default,
                        mut_restriction: MutRestriction {
                            kind: RestrictionKind::Unrestricted,
                            span: DUMMY_SP,
                        },
                        default: None,
                    })),
                    ident: Some(Ident::from_str(fname)),
                    ty: Box::new(Ty {
                        id: NodeId::from_u32(0),
                        kind: TyKind::Path(None, Path::from_ident(Ident::with_dummy_span(fty))),
                        span: DUMMY_SP,
                    }),
                    id: NodeId::from_u32(0),
                    span: DUMMY_SP,
                    is_placeholder: false,
                }
            }
            #[cfg(not(rapx_has_fielddef_extras))]
            {
                FieldDef {
                    attrs: set_attrs(build_std),
                    vis: Visibility {
                        span: DUMMY_SP,
                        kind: VisibilityKind::Public,
                        #[cfg(not(rapx_rustc_ge_199))]
                        tokens: None,
                    },
                    #[cfg(rapx_rustc_ge_198)]
                    mut_restriction: MutRestriction {
                        kind: RestrictionKind::Unrestricted,
                        span: DUMMY_SP,
                        #[cfg(not(rapx_rustc_ge_199))]
                        tokens: None,
                    },
                    ident: Some(Ident::from_str(fname)),
                    ty: Box::new(Ty {
                        id: NodeId::from_u32(0),
                        kind: TyKind::Path(None, Path::from_ident(Ident::with_dummy_span(fty))),
                        span: DUMMY_SP,
                        #[cfg(not(rapx_rustc_ge_199))]
                        tokens: None,
                    }),
                    id: NodeId::from_u32(0),
                    span: DUMMY_SP,
                    is_placeholder: false,
                    safety: Safety::Default,
                    default: None,
                }
            }
        })
        .collect();

    let ident = Ident {
        name: Symbol::intern(name),
        span: DUMMY_SP,
    };
    let variant_data = VariantData::Struct {
        fields,
        recovered: Recovered::No,
    };

    let item_kind = ItemKind::Struct(ident, Generics::default(), variant_data);

    Box::new(Item {
        attrs: set_attrs(build_std),
        id: NodeId::from_u32(0),
        kind: item_kind,
        vis: Visibility {
            span: DUMMY_SP,
            kind: VisibilityKind::Public,
            #[cfg(not(rapx_rustc_ge_199))]
            tokens: None,
        },
        span: DUMMY_SP,
        tokens: None,
    })
}
