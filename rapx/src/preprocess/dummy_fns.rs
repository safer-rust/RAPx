use super::set_attrs;
use rustc_ast::*;
use rustc_span::{DUMMY_SP, symbol::Ident};
use thin_vec::ThinVec;

fn make_dummy_fn_sig() -> FnSig {
    let fn_decl = FnDecl {
        inputs: ThinVec::new(),
        output: FnRetTy::Default(DUMMY_SP),
    };

    FnSig {
        decl: Box::new(fn_decl),
        header: FnHeader {
            safety: Safety::Default,
            constness: Const::No,
            ext: Extern::None,
            #[cfg(rapx_ge_100)]
            coroutine_marker: None,
            #[cfg(not(rapx_ge_100))]
            coroutine_kind: None,
        },
        span: DUMMY_SP,
    }
}

fn make_dummy_block() -> Block {
    Block {
        stmts: ThinVec::new(),
        id: DUMMY_NODE_ID,
        rules: BlockCheckMode::Default,
        span: DUMMY_SP,
        #[cfg(not(rapx_ge_99))]
        tokens: None,
    }
}

fn make_dummy_fn(ident_name: &str, build_std: bool) -> Box<Item> {
    let ident = Ident::from_str(ident_name);

    let fn_ast = Fn {
        #[cfg(rapx_ge_99)]
        defaultness: Defaultness::Implicit,
        #[cfg(not(rapx_ge_99))]
        defaultness: Defaultness::Final,
        ident,
        generics: Generics::default(),
        sig: make_dummy_fn_sig(),
        contract: None,
        define_opaque: None,
        #[cfg(rapx_ge_100)]
        eii_impl: Default::default(),
        #[cfg(all(rapx_ge_99, not(rapx_ge_100)))]
        eii_impls: Default::default(),
        body: Some(Box::new(make_dummy_block())),
    };

    Box::new(Item {
        attrs: set_attrs(build_std),
        id: DUMMY_NODE_ID,
        kind: ItemKind::Fn(Box::new(fn_ast)),
        vis: Visibility {
            span: DUMMY_SP,
            kind: VisibilityKind::Public,
            #[cfg(not(rapx_ge_99))]
            tokens: None,
        },
        span: DUMMY_SP,
        tokens: None,
    })
}

pub(crate) fn create_dummy_fns(krate: &mut Crate, build_std: bool) {
    let raw_ptr_fn = make_dummy_fn("__raw_ptr_deref_dummy", build_std);
    let static_mut_fn = make_dummy_fn("__static_mut_deref_dummy", build_std);

    krate.items.push(raw_ptr_fn);
    krate.items.push(static_mut_fn);
}
