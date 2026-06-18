use rustc_hir::HirId;
use rustc_hir::PrimTy;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::{ImplItemId, ItemKind, Mutability, Node, OwnerId, TraitItemId};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::fast_reject::SimplifiedType;
use rustc_middle::ty::{FloatTy, IntTy, UintTy};
use rustc_span::symbol::{Ident, Symbol};

pub fn path_str_def_id<'tcx>(tcx: TyCtxt<'tcx>, path_str: &str) -> DefId {
    let path: Vec<&str> = path_str.split("::").collect();
    def_path_last_def_id(&tcx, &path)
}

fn def_path_last_def_id<'tcx>(tcx: &TyCtxt<'tcx>, path: &[&str]) -> DefId {
    def_path_def_ids(tcx, path)
        .last()
        .expect(&format!("can not resolve {:?}", path))
}

pub struct DefPath {
    def_ids: Vec<DefId>,
}

impl DefPath {
    //path like "std::vec::Vec"
    pub fn new(raw: &str, tcx: &TyCtxt<'_>) -> Self {
        let path: Vec<&str> = raw.split("::").collect();
        let def_ids: Vec<DefId> = def_path_def_ids(tcx, &path).collect();
        if def_ids.len() == 0 {
            panic!("Fail to parse def path {}", raw);
        }
        DefPath { def_ids }
    }

    pub fn last_def_id(&self) -> DefId {
        *self.def_ids.last().unwrap()
    }
}

/* Modified from Clippy
 * https://github.com/rust-lang/rust-clippy/blob/6d61bd/clippy_utils/src/lib.rs
 * Note: Commit 6b61bd matches rustc nightly 2024-06-30
 * */

/// Resolves a def path like `std::vec::Vec` to its [`DefId`]s, see [`def_path_res`].
fn def_path_def_ids(tcx: &TyCtxt<'_>, path: &[&str]) -> impl Iterator<Item = DefId> {
    def_path_res(tcx, path)
        .into_iter()
        .filter_map(|res| res.opt_def_id())
}

fn def_path_res(tcx: &TyCtxt<'_>, path: &[&str]) -> Vec<Res> {
    let (base, path) = match path {
        [primitive] => {
            return vec![
                PrimTy::from_name(Symbol::intern(primitive)).map_or(Res::Err, Res::PrimTy),
            ];
        }
        [base, path @ ..] => (base, path),
        _ => return Vec::new(),
    };

    let base_sym = Symbol::intern(base);

    let local_crate = if tcx.crate_name(LOCAL_CRATE) == base_sym {
        Some(LOCAL_CRATE.as_def_id())
    } else {
        None
    };

    let crates = find_primitive_impls(tcx, base)
        .chain(local_crate)
        .map(|id| Res::Def(tcx.def_kind(id), id))
        .chain(find_crates(tcx, base_sym))
        .collect();

    def_path_res_with_base(tcx, crates, path)
}

fn def_path_res_with_base(tcx: &TyCtxt<'_>, mut base: Vec<Res>, mut path: &[&str]) -> Vec<Res> {
    while let [segment, rest @ ..] = path {
        path = rest;
        let segment = Symbol::intern(segment);

        base = base
            .into_iter()
            .filter_map(|res| res.opt_def_id())
            .flat_map(|def_id| {
                // When the current def_id is e.g. `struct S`, check the impl items in
                // `impl S { ... }`
                let inherent_impl_children = tcx
                    .inherent_impls(def_id)
                    .iter()
                    .flat_map(|&impl_def_id| item_children_by_name(tcx, impl_def_id, segment));

                let direct_children = item_children_by_name(tcx, def_id, segment);

                inherent_impl_children.chain(direct_children)
            })
            .collect();
    }

    base
}

fn find_primitive_impls<'tcx>(
    tcx: &TyCtxt<'tcx>,
    name: &str,
) -> impl Iterator<Item = DefId> + 'tcx {
    let ty = match name {
        "bool" => SimplifiedType::Bool,
        "char" => SimplifiedType::Char,
        "str" => SimplifiedType::Str,
        "array" => SimplifiedType::Array,
        "slice" => SimplifiedType::Slice,
        // FIXME: rustdoc documents these two using just `pointer`.
        //
        // Maybe this is something we should do here too.
        "const_ptr" => SimplifiedType::Ptr(Mutability::Not),
        "mut_ptr" => SimplifiedType::Ptr(Mutability::Mut),
        "isize" => SimplifiedType::Int(IntTy::Isize),
        "i8" => SimplifiedType::Int(IntTy::I8),
        "i16" => SimplifiedType::Int(IntTy::I16),
        "i32" => SimplifiedType::Int(IntTy::I32),
        "i64" => SimplifiedType::Int(IntTy::I64),
        "i128" => SimplifiedType::Int(IntTy::I128),
        "usize" => SimplifiedType::Uint(UintTy::Usize),
        "u8" => SimplifiedType::Uint(UintTy::U8),
        "u16" => SimplifiedType::Uint(UintTy::U16),
        "u32" => SimplifiedType::Uint(UintTy::U32),
        "u64" => SimplifiedType::Uint(UintTy::U64),
        "u128" => SimplifiedType::Uint(UintTy::U128),
        "f32" => SimplifiedType::Float(FloatTy::F32),
        "f64" => SimplifiedType::Float(FloatTy::F64),
        _ => {
            return [].iter().copied();
        }
    };

    tcx.incoherent_impls(ty).iter().copied()
}

fn non_local_item_children_by_name(tcx: &TyCtxt<'_>, def_id: DefId, name: Symbol) -> Vec<Res> {
    match tcx.def_kind(def_id) {
        DefKind::Mod | DefKind::Enum | DefKind::Trait => tcx
            .module_children(def_id)
            .iter()
            .filter(|item| item.ident.name == name)
            .map(|child| child.res.expect_non_local())
            .collect(),
        DefKind::Impl { .. } => tcx
            .associated_item_def_ids(def_id)
            .iter()
            .copied()
            .filter(|assoc_def_id| tcx.item_name(*assoc_def_id) == name)
            .map(|assoc_def_id| Res::Def(tcx.def_kind(assoc_def_id), assoc_def_id))
            .collect(),
        _ => Vec::new(),
    }
}

fn local_item_children_by_name(tcx: &TyCtxt<'_>, local_id: LocalDefId, name: Symbol) -> Vec<Res> {
    let root_mod;
    let hir_node = tcx.hir_node_by_def_id(local_id);
    let item_kind = match hir_node {
        Node::Crate(module) => {
            root_mod = ItemKind::Mod(hir_node.ident().unwrap(), module);
            &root_mod
        }
        Node::Item(item) => &item.kind,
        _ => return Vec::new(),
    };

    let res = |ident: Ident, owner_id: OwnerId| {
        if ident.name == name {
            let def_id = owner_id.to_def_id();
            Some(Res::Def(tcx.def_kind(def_id), def_id))
        } else {
            None
        }
    };

    match item_kind {
        ItemKind::Mod(_ident, module) => module
            .item_ids
            .iter()
            .filter_map(|&item_id| res(tcx.hir_ident(item_id.hir_id()), item_id.owner_id))
            .collect(),
        ItemKind::Impl(r#impl) => r#impl
            .items
            .iter()
            .filter_map(|&ImplItemId { owner_id }| {
                res(tcx.hir_ident(HirId::from(owner_id)), owner_id)
            })
            .collect(),
        #[cfg(not(rapx_rustc_ge_198))]
        ItemKind::Trait(.., trait_item_refs) => trait_item_refs
            .iter()
            .filter_map(|&TraitItemId { owner_id }| {
                res(tcx.hir_ident(HirId::from(owner_id)), owner_id)
            })
            .collect(),
        #[cfg(rapx_rustc_ge_198)]
        ItemKind::Trait {
            items: trait_item_refs,
            ..
        } => trait_item_refs
            .iter()
            .filter_map(|&TraitItemId { owner_id }| {
                res(tcx.hir_ident(HirId::from(owner_id)), owner_id)
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn item_children_by_name(tcx: &TyCtxt<'_>, def_id: DefId, name: Symbol) -> Vec<Res> {
    if let Some(local_id) = def_id.as_local() {
        local_item_children_by_name(tcx, local_id, name)
    } else {
        non_local_item_children_by_name(tcx, def_id, name)
    }
}

fn find_crates(tcx: &TyCtxt<'_>, name: Symbol) -> Vec<Res> {
    tcx.crates(())
        .iter()
        .copied()
        .filter(move |&num| tcx.crate_name(num) == name)
        .map(CrateNum::as_def_id)
        .map(|id| Res::Def(tcx.def_kind(id), id))
        .collect()
}
