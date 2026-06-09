use rustc_abi::VariantIdx;
use rustc_middle::{
    mir::{
        BasicBlock, BasicBlockData, Body, Local, LocalDecl, Operand, TerminatorKind,
        visit::{TyContext, Visitor},
    },
    ty::{
        self, EarlyBinder, GenericArgKind, InstanceKind::Item, Ty, TyCtxt, TyKind,
        TypeSuperVisitable, TypeVisitable, TypeVisitor,
    },
};
use rustc_span::def_id::DefId;
use std::{collections::HashMap, ops::ControlFlow};

use super::*;

pub struct OwnedHeapAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    adt_heap: OHAResultMap,
    fn_set: HashSet<DefId>,
    ty_map: HashMap<Ty<'tcx>, String>,
    adt_recorder: HashSet<DefId>,
}

impl<'tcx> Analysis for OwnedHeapAnalyzer<'tcx> {
    fn name(&self) -> &'static str {
        "Default heap analysis."
    }
    fn run(&mut self) {
        self.start();
    }
    fn reset(&mut self) {
        todo!();
    }
}

impl<'tcx> OwnedHeapAnalysis for OwnedHeapAnalyzer<'tcx> {
    fn get_all_items(&self) -> OHAResultMap {
        self.adt_heap.clone()
    }
}

// This function is aiming at resolving problems due to 'TyContext' not implementing 'Clone' trait,
// thus we call function 'copy_ty_context' to simulate 'self.clone()'.
#[inline(always)]
pub(crate) fn copy_ty_context(tc: &TyContext) -> TyContext {
    match tc {
        TyContext::LocalDecl { local, source_info } => TyContext::LocalDecl {
            local: local.clone(),
            source_info: source_info.clone(),
        },
        _ => unreachable!(),
    }
}

impl<'tcx> OwnedHeapAnalyzer<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            adt_heap: HashMap::default(),
            fn_set: HashSet::new(),
            ty_map: HashMap::new(),
            adt_recorder: HashSet::new(),
        }
    }

    pub fn ty_map(&self) -> &HashMap<Ty<'tcx>, String> {
        &self.ty_map
    }

    pub fn ty_map_mut(&mut self) -> &mut HashMap<Ty<'tcx>, String> {
        &mut self.ty_map
    }

    pub fn fn_set(&self) -> &HashSet<DefId> {
        &self.fn_set
    }

    pub fn fn_set_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.fn_set
    }

    pub fn adt_recorder(&self) -> &HashSet<DefId> {
        &self.adt_recorder
    }

    pub fn adt_recorder_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.adt_recorder
    }

    pub fn adt_heap(&self) -> &OHAResultMap {
        &self.adt_heap
    }

    pub fn adt_heap_mut(&mut self) -> &mut OHAResultMap {
        &mut self.adt_heap
    }

    pub fn format_heap_unit(unit: &(OwnedHeap, Vec<bool>)) -> String {
        let (heap, flags) = unit;
        let vec_str = flags
            .iter()
            .map(|&b| if b { "1" } else { "0" })
            .collect::<Vec<_>>()
            .join(",");
        format!("({}, [{}])", heap, vec_str)
    }

    pub fn output(&mut self) {
        for elem in self.adt_heap() {
            let name = format!("{:?}", EarlyBinder::skip_binder(self.tcx.type_of(*elem.0)));
            let owning = elem
                .1
                .iter()
                .map(Self::format_heap_unit)
                .collect::<Vec<_>>()
                .join(", ");
            rap_info!("{} {}", name, owning);
        }
    }

    // From the top-down method of our approach, this 'visitor' is the set of several sub-phases
    // which means it contains multiple sub-visitors to make whole method 'self.visitor()' work.
    //
    // For example, given an adtef (like Vec<T>), the result of 'visitor' contains two parts:
    //
    //     pt1 Enum:  {True / UnTrue} indicates whether it will directly have a heap data
    //     pt2 Array: [bool;N] indicates whether each generic parameter will have a raw param
    //
    // Those 2 parts can accelerate heap-heap inference in the data-flow analysis.
    pub fn start(&mut self) {
        #[inline(always)]
        fn start_channel<M>(mut method: M, v_did: &Vec<DefId>)
        where
            M: FnMut(DefId) -> (),
        {
            for did in v_did {
                method(*did);
            }
        }

        #[inline(always)]
        fn show_heap(ref_type_analysis: &mut OwnedHeapAnalyzer) {
            for elem in ref_type_analysis.adt_heap() {
                let name = format!(
                    "{:?}",
                    EarlyBinder::skip_binder(ref_type_analysis.tcx.type_of(*elem.0))
                );
                let owning = format!("{:?}", elem.1);
                rap_debug!("ADT analysis: {} {}", name, owning);
            }
        }

        // Get the Global TyCtxt from rustc
        // Grasp all mir Keys defined in current crate
        let tcx = self.tcx;
        let mir_keys = tcx.mir_keys(());

        for each_mir in mir_keys {
            // Get the defid of current crate and get mir Body through this id
            let def_id = each_mir.to_def_id();
            let body = tcx.instance_mir(Item(def_id));

            // Insert the defid to hashset if is not existed and visit the body
            if self.fn_set_mut().insert(def_id) {
                self.visit_body(body);
            } else {
                continue;
            }
        }

        let dids: Vec<DefId> = self.adt_recorder.iter().map(|did| *did).collect();

        start_channel(|did| self.extract_raw_generic(did), &dids);
        start_channel(|did| self.extract_raw_generic_prop(did), &dids);
        start_channel(|did| self.extract_phantom_unit(did), &dids);
        start_channel(|did| self.extract_heap_prop(did), &dids);

        show_heap(self);
    }

    // Extract params in adt types, the 'param' means one generic parameter acting like 'T', 'A', etc...
    // In the sub-visitor RawGeneric, it will visit the given type recursively, and extract all params.
    //
    // Note that RAP is only interested in 'raw' params ('T' not like '*mut T').
    // It lies in 'one-entire field' | recursive in tuple | recursive in array | mixed before
    //
    // Given a struct Example<A, B, T, S>:
    //
    // struct Example<A, B, T, S> {
    //     a: A,
    //     b: (i32, (f64, B)),
    //     c: [[(S) ; 1] ; 2],
    //     d: Vec<T>,
    // }
    //
    // the final result for <A, B, T, S> is <true, true, false, true>.
    #[inline(always)]
    fn extract_raw_generic(&mut self, did: DefId) {
        // Get the definition and subset reference from adt did
        let ty = EarlyBinder::skip_binder(self.tcx.type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        let mut v_res = Vec::new();

        for variant in adt_def.variants().iter() {
            let mut raw_generic = IsolatedParam::new(substs.len());

            for field in &variant.fields {
                let field_ty = field.ty(self.tcx, substs);
                let _ = field_ty.visit_with(&mut raw_generic);
            }
            v_res.push((OwnedHeap::False, raw_generic.record_mut().clone()));
        }

        self.adt_heap_mut().insert(did, v_res);
    }

    // Extract all params in the adt types like param 'T' and then propagate from the bottom to top.
    // This procedural is the successor of `extract_raw_generic`, and the main idea of RawGenericPropagation
    // is to propagate params from bottom adt to the top as well as updating Analysis Context.
    //
    // Note that it will thorough consider mono-morphization existed in adt-def.
    // That means the type 'Vec<T>', 'Vec<Vec<T>>' and 'Vec<i32>' are totally different!!!!
    //
    // Given a struct Example<A, B, T, S>:
    //
    // struct X<A> {
    //     a: A,
    // }
    // the final result for <A> is <true>.
    //
    // struct Y1<B> {
    //     a: (i32, (f64, B)),
    //     b: X<i32>,
    // }
    // the final result for <B> is <true>.
    //
    // struct Example<A, B, T, S> {
    //     a: X<A>,
    //     b: (i32, (f64, B)),
    //     c: [[(S) ; 1] ; 2],
    //     d: Vec<T>,
    // }
    //
    // the final result for <A, B, T, S> is <true, true, false, true>.
    #[inline(always)]
    fn extract_raw_generic_prop(&mut self, did: DefId) {
        // Get the definition and subset reference from adt did
        let ty = EarlyBinder::skip_binder(self.tcx.type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        let source_enum = adt_def.is_enum();

        let mut v_res = self.adt_heap_mut().get_mut(&did).unwrap().clone();

        for (variant_index, variant) in adt_def.variants().iter().enumerate() {
            let res = v_res[variant_index as usize].clone();

            let mut raw_generic_prop = IsolatedParamPropagation::new(
                self.tcx,
                res.1.clone(),
                source_enum,
                self.adt_heap(),
            );

            for field in &variant.fields {
                let field_ty = field.ty(self.tcx, substs);
                let _ = field_ty.visit_with(&mut raw_generic_prop);
            }
            v_res[variant_index as usize] =
                (OwnedHeap::False, raw_generic_prop.record_mut().clone());
        }

        self.adt_heap_mut().insert(did, v_res);
    }

    // Extract all types that include PhantomData<T> which T must be a raw Param
    // Consider these types as a unit to guide the traversal over adt types
    #[inline(always)]
    fn extract_phantom_unit(&mut self, did: DefId) {
        // Get ty from defid and the ty is made up with generic type
        let ty = EarlyBinder::skip_binder(self.tcx.type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        // As for one heap-allocation unit, only struct will contains the information that we want
        // Example:
        // struct Foo<T> {
        //     NonNull<T>,      // this indicates a pointer
        //     PhantomData<T>,  // this indicates a heap
        // }
        if adt_def.is_struct() {
            let mut res = self.adt_heap_mut().get_mut(&did).unwrap()[0].clone();
            // Extract all fields in one given struct
            for field in adt_def.all_fields() {
                let field_ty = field.ty(self.tcx, substs);
                match field_ty.kind() {
                    // Filter the field which is also a struct due to PhantomData<T> is struct
                    TyKind::Adt(field_adt_def, field_substs) => {
                        if field_adt_def.is_phantom_data() {
                            // Extract all generic args in the type
                            for generic_arg in *field_substs {
                                match generic_arg.kind() {
                                    GenericArgKind::Type(g_ty) => {
                                        let mut raw_generic_field_subst =
                                            IsolatedParamFieldSubst::new();
                                        let _ = g_ty.visit_with(&mut raw_generic_field_subst);
                                        if raw_generic_field_subst.contains_param() {
                                            {
                                                // To enhance the soundness of phantom unit, the struct should have a
                                                // pointer to store T
                                                let mut has_ptr = false;
                                                for field in adt_def.all_fields() {
                                                    let field_ty = field.ty(self.tcx, substs);
                                                    let mut find_ptr = FindPtr::new(self.tcx);
                                                    let _ = field_ty.visit_with(&mut find_ptr);
                                                    if find_ptr.has_ptr() {
                                                        has_ptr = true;
                                                        break;
                                                    }
                                                }
                                                if has_ptr == false {
                                                    return;
                                                }
                                            }

                                            res.0 = OwnedHeap::True;
                                            self.adt_heap_mut().insert(did, vec![res.clone()]);
                                            return;
                                        }
                                    }
                                    GenericArgKind::Lifetime(..) => {
                                        return;
                                    }
                                    GenericArgKind::Const(..) => {
                                        return;
                                    }
                                }
                            }
                        }
                    }
                    _ => continue,
                }
            }
        }
    }

    #[inline(always)]
    fn extract_heap_prop(&mut self, did: DefId) {
        // Get the definition and subset reference from adt did
        let ty = EarlyBinder::skip_binder(self.tcx.type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        let mut v_res = self.adt_heap_mut().get_mut(&did).unwrap().clone();

        for (variant_index, variant) in adt_def.variants().iter().enumerate() {
            let res = v_res[variant_index as usize].clone();

            let mut heap_prop = HeapPropagation::new(self.tcx, res.0, self.adt_heap());

            for field in &variant.fields {
                let field_ty = field.ty(self.tcx, substs);
                let _ = field_ty.visit_with(&mut heap_prop);
            }
            v_res[variant_index as usize].0 = heap_prop.heap();
        }

        self.adt_heap_mut().insert(did, v_res);
    }
}

impl<'tcx> Visitor<'tcx> for OwnedHeapAnalyzer<'tcx> {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        for (local, local_decl) in body.local_decls.iter().enumerate() {
            self.visit_local_decl(Local::from(local), local_decl);
        }

        for (block, data) in body.basic_blocks.iter().enumerate() {
            self.visit_basic_block_data(BasicBlock::from(block), data);
        }
    }

    fn visit_basic_block_data(&mut self, _block: BasicBlock, data: &BasicBlockData<'tcx>) {
        let term = data.terminator();
        match &term.kind {
            TerminatorKind::Call { func, .. } => match func {
                Operand::Constant(constant) => match constant.ty().kind() {
                    ty::FnDef(def_id, ..) => {
                        if self.tcx.is_mir_available(*def_id) && self.fn_set_mut().insert(*def_id) {
                            let body = self.tcx.instance_mir(Item(*def_id));
                            self.visit_body(body);
                        }
                    }
                    _ => (),
                },
                _ => (),
            },
            _ => (),
        }
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>, ty_context: TyContext) {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if self.ty_map().get(&ty).is_some() {
                    return;
                }
                self.ty_map_mut().insert(ty, format!("{:?}", ty));
                self.adt_recorder_mut().insert(adtdef.did());

                for field in adtdef.all_fields() {
                    self.visit_ty(field.ty(self.tcx, substs), copy_ty_context(&ty_context))
                }

                for ty in substs.types() {
                    self.visit_ty(ty, copy_ty_context(&ty_context));
                }
            }
            TyKind::Array(ty, ..) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::Slice(ty) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::RawPtr(ty, _) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::Ref(_, ty, ..) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::Tuple(tuple_fields) => {
                for field in tuple_fields.iter() {
                    self.visit_ty(field, copy_ty_context(&ty_context));
                }
            }
            _ => return,
        }
    }

    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        let ty_context = TyContext::LocalDecl {
            local,
            source_info: local_decl.source_info,
        };
        self.visit_ty(local_decl.ty, ty_context);
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for IsolatedParam {
    type Result = ControlFlow<()>;
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::Param(param_ty) => {
                self.record_mut()[param_ty.index as usize] = true;
                ControlFlow::Continue(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for IsolatedParamFieldSubst {
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::Adt(..) => ty.super_visit_with(self),
            TyKind::Param(param_ty) => {
                self.parameters_mut().insert(param_ty.index as usize);
                ControlFlow::Continue(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for IsolatedParamPropagation<'tcx, 'a> {
    // #[inline(always)]
    // fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
    //     Some(self.tcx)
    // }
    type Result = ControlFlow<()>;

    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if substs.len() == 0 {
                    return ControlFlow::Break(());
                }

                if !self.source_enum() && adtdef.is_enum() {
                    return ControlFlow::Break(());
                }

                if !self.unique_mut().insert(adtdef.did()) {
                    return ControlFlow::Continue(());
                }

                let mut map_raw_generic_field_subst = HashMap::new();
                for (index, subst) in substs.iter().enumerate() {
                    match subst.kind() {
                        GenericArgKind::Lifetime(..) => continue,
                        GenericArgKind::Const(..) => continue,
                        GenericArgKind::Type(g_ty) => {
                            let mut raw_generic_field_subst = IsolatedParamFieldSubst::new();
                            let _ = g_ty.visit_with(&mut raw_generic_field_subst);
                            if !raw_generic_field_subst.contains_param() {
                                continue;
                            }
                            map_raw_generic_field_subst
                                .insert(index as usize, raw_generic_field_subst);
                        }
                    }
                }
                if map_raw_generic_field_subst.is_empty() {
                    return ControlFlow::Break(());
                }

                let get_ans = self.heap().get(&adtdef.did()).unwrap();
                if get_ans.len() == 0 {
                    return ControlFlow::Break(());
                }
                let get_ans = get_ans[0].clone();

                for (index, flag) in get_ans.1.iter().enumerate() {
                    if *flag && map_raw_generic_field_subst.contains_key(&index) {
                        for elem in map_raw_generic_field_subst
                            .get(&index)
                            .unwrap()
                            .parameters()
                        {
                            self.record[*elem] = true;
                        }
                    }
                }

                for field in adtdef.all_fields() {
                    let field_ty = field.ty(self.tcx, substs);
                    let _ = field_ty.visit_with(self);
                }

                self.unique_mut().remove(&adtdef.did());

                ty.super_visit_with(self)
            }
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for HeapPropagation<'tcx, 'a> {
    // #[inline(always)]
    // fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
    //     Some(self.tcx)
    // }
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if !self.unique_mut().insert(adtdef.did()) {
                    return ControlFlow::Continue(());
                }

                if adtdef.is_enum() {
                    return ControlFlow::Break(());
                }

                let get_ans = self.heap_res().get(&adtdef.did()).unwrap();
                if get_ans.len() == 0 {
                    return ControlFlow::Break(());
                }
                let get_ans = get_ans[0].clone();

                match get_ans.0 {
                    OwnedHeap::True => {
                        self.heap = OwnedHeap::True;
                        return ControlFlow::Break(());
                    }
                    _ => (),
                };

                for field in adtdef.all_fields() {
                    let field_ty = field.ty(self.tcx, substs);
                    let _ = field_ty.visit_with(self);
                }

                self.unique_mut().remove(&adtdef.did());

                ty.super_visit_with(self)
            }
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for FindPtr<'tcx> {
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if adtdef.is_struct() {
                    if !self.unique_mut().insert(adtdef.did()) {
                        return ControlFlow::Continue(());
                    }

                    for field in adtdef.all_fields() {
                        let field_ty = field.ty(self.tcx, substs);
                        let _ = field_ty.visit_with(self);
                    }
                    self.unique_mut().remove(&adtdef.did());
                }
                ControlFlow::Continue(())
            }
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::RawPtr(..) => {
                self.set_ptr(true);
                ControlFlow::Break(())
            }
            TyKind::Ref(..) => {
                self.set_ptr(true);
                ControlFlow::Break(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for DefaultOwnership<'tcx, 'a> {
    // #[inline(always)]
    // fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
    //     Some(self.tcx)
    // }
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if adtdef.is_enum() {
                    return ControlFlow::Break(());
                }

                if !self.unique_mut().insert(adtdef.did()) {
                    return ControlFlow::Continue(());
                }

                let get_ans = self.heap().get(&adtdef.did()).unwrap();

                // handle the secene of Zero Sized Types
                if get_ans.len() == 0 {
                    return ControlFlow::Break(());
                }
                let (unit_res, generic_list) = get_ans[0].clone();

                match unit_res {
                    OwnedHeap::True => {
                        self.set_res(OwnedHeap::True);
                        return ControlFlow::Break(());
                    }
                    OwnedHeap::False => {
                        for (index, each_generic) in generic_list.iter().enumerate() {
                            if *each_generic == false {
                                continue;
                            } else {
                                let subset_ty = substs[index].expect_ty();
                                self.unique_mut().remove(&adtdef.did());
                                let _ = subset_ty.visit_with(self);
                            }
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                }
                ControlFlow::Continue(())
            }
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::Param(..) => {
                self.set_param(true);
                self.set_res(OwnedHeap::True);
                ControlFlow::Break(())
            }
            TyKind::RawPtr(..) => {
                self.set_ptr(true);
                ControlFlow::Continue(())
            }
            TyKind::Ref(..) => {
                self.set_ptr(true);
                ControlFlow::Continue(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Default)]
pub struct TyWithIndex<'tcx>(pub Option<(usize, &'tcx TyKind<'tcx>, Option<usize>, bool)>);

impl<'tcx> TyWithIndex<'tcx> {
    pub fn new(ty: Ty<'tcx>, vidx: Option<VariantIdx>) -> Self {
        match &ty.kind() {
            TyKind::Tuple(list) => TyWithIndex(Some((list.len(), &ty.kind(), None, true))),
            TyKind::Adt(adtdef, ..) => {
                if adtdef.is_enum() {
                    if vidx.is_none() {
                        return TyWithIndex(None);
                    }
                    let idx = vidx.unwrap();
                    let len = adtdef.variants()[idx].fields.len();
                    TyWithIndex(Some((len, &ty.kind(), Some(idx.index()), true)))
                } else {
                    let len = adtdef.variants()[VariantIdx::from_usize(0)].fields.len();
                    TyWithIndex(Some((len, &ty.kind(), None, true)))
                }
            }
            TyKind::Array(..) | TyKind::Param(..) | TyKind::RawPtr(..) | TyKind::Ref(..) => {
                TyWithIndex(Some((1, &ty.kind(), None, true)))
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(..)
            | TyKind::Uint(..)
            | TyKind::Float(..)
            | TyKind::Str
            | TyKind::Slice(..) => TyWithIndex(Some((1, &ty.kind(), None, false))),
            _ => TyWithIndex(None),
        }
    }

    // 0->unsupported, 1->trivial, 2-> needed
    pub fn get_priority(&self) -> usize {
        if self.0.is_none() {
            return 0;
        }
        match self.0.unwrap().0 {
            0 => 1,
            _ => match self.0.unwrap().3 {
                true => 2,
                false => 1,
            },
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Encoder;

impl<'tcx> Encoder {
    pub fn encode(
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
        adt_heap: OHAResultMap,
        variant: Option<VariantIdx>,
    ) -> OwnershipLayoutResult {
        match ty.kind() {
            TyKind::Array(..) => {
                let mut res = OwnershipLayoutResult::new();
                let mut default_heap = DefaultOwnership::new(tcx, &adt_heap);

                let _ = ty.visit_with(&mut default_heap);
                res.update_from_default_heap_visitor(&mut default_heap);

                res
            }
            TyKind::Tuple(tuple_ty_list) => {
                let mut res = OwnershipLayoutResult::new();

                for tuple_ty in tuple_ty_list.iter() {
                    let mut default_heap = DefaultOwnership::new(tcx, &adt_heap);

                    let _ = tuple_ty.visit_with(&mut default_heap);
                    res.update_from_default_heap_visitor(&mut default_heap);
                }

                res
            }
            TyKind::Adt(adtdef, substs) => {
                // check the ty is or is not an enum and the variant of this enum is or is not given
                if adtdef.is_enum() && variant.is_none() {
                    return OwnershipLayoutResult::new();
                }

                let mut res = OwnershipLayoutResult::new();

                // check the ty if it is a struct or union
                if adtdef.is_struct() || adtdef.is_union() {
                    for field in adtdef.all_fields() {
                        let field_ty = field.ty(tcx, substs);

                        let mut default_heap = DefaultOwnership::new(tcx, &adt_heap);

                        let _ = field_ty.visit_with(&mut default_heap);
                        res.update_from_default_heap_visitor(&mut default_heap);
                    }
                }
                // check the ty which is an enum with a exact variant idx
                else if adtdef.is_enum() {
                    let vidx = variant.unwrap();

                    for field in &adtdef.variants()[vidx].fields {
                        let field_ty = field.ty(tcx, substs);

                        let mut default_heap = DefaultOwnership::new(tcx, &adt_heap);

                        let _ = field_ty.visit_with(&mut default_heap);
                        res.update_from_default_heap_visitor(&mut default_heap);
                    }
                }
                res
            }
            TyKind::Param(..) => {
                let mut res = OwnershipLayoutResult::new();
                res.set_requirement(true);
                res.set_param(true);
                res.set_owned(true);
                res.layout_mut().push(OwnedHeap::True);
                res
            }
            TyKind::RawPtr(..) => {
                let mut res = OwnershipLayoutResult::new();
                res.set_requirement(true);
                res.layout_mut().push(OwnedHeap::False);
                res
            }
            TyKind::Ref(..) => {
                let mut res = OwnershipLayoutResult::new();
                res.set_requirement(true);
                res.layout_mut().push(OwnedHeap::False);
                res
            }
            _ => OwnershipLayoutResult::new(),
        }
    }
}

#[derive(Clone)]
struct IsolatedParamFieldSubst {
    parameters: HashSet<usize>,
}

impl<'tcx> IsolatedParamFieldSubst {
    pub fn new() -> Self {
        Self {
            parameters: HashSet::new(),
        }
    }

    pub fn parameters(&self) -> &HashSet<usize> {
        &self.parameters
    }

    pub fn parameters_mut(&mut self) -> &mut HashSet<usize> {
        &mut self.parameters
    }

    pub fn contains_param(&self) -> bool {
        !self.parameters.is_empty()
    }
}

#[derive(Clone)]
struct IsolatedParamPropagation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    record: Vec<bool>,
    unique: HashSet<DefId>,
    source_enum: bool,
    ref_adt_heap: &'a OHAResultMap,
}

impl<'tcx, 'a> IsolatedParamPropagation<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        record: Vec<bool>,
        source_enum: bool,
        ref_adt_heap: &'a OHAResultMap,
    ) -> Self {
        Self {
            tcx,
            record,
            unique: HashSet::new(),
            source_enum,
            ref_adt_heap,
        }
    }

    pub fn record_mut(&mut self) -> &mut Vec<bool> {
        &mut self.record
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn source_enum(&mut self) -> bool {
        self.source_enum
    }

    pub fn heap(&self) -> &'a OHAResultMap {
        self.ref_adt_heap
    }
}

#[derive(Clone)]
struct HeapPropagation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    heap: OwnedHeap,
    unique: HashSet<DefId>,
    heap_res: &'a OHAResultMap,
}

impl<'tcx, 'a> HeapPropagation<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, heap: OwnedHeap, heap_res: &'a OHAResultMap) -> Self {
        Self {
            tcx,
            heap,
            unique: HashSet::new(),
            heap_res,
        }
    }

    pub fn heap(&self) -> OwnedHeap {
        self.heap
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn heap_res(&self) -> &'a OHAResultMap {
        self.heap_res
    }
}

#[derive(Clone)]
struct IsolatedParam {
    record: Vec<bool>,
}

impl IsolatedParam {
    pub fn new(len: usize) -> Self {
        Self {
            record: vec![false; len],
        }
    }

    pub fn record_mut(&mut self) -> &mut Vec<bool> {
        &mut self.record
    }
}

#[derive(Clone)]
pub struct DefaultOwnership<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    unique: HashSet<DefId>,
    ref_adt_heap: &'a OHAResultMap,
    res: OwnedHeap,
    param: bool,
    ptr: bool,
}

impl<'tcx, 'a> DefaultOwnership<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, ref_adt_heap: &'a OHAResultMap) -> Self {
        Self {
            tcx,
            unique: HashSet::new(),
            ref_adt_heap,
            res: OwnedHeap::False,
            param: false,
            ptr: false,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn unique(&self) -> &HashSet<DefId> {
        &self.unique
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn get_res(&self) -> OwnedHeap {
        self.res
    }

    pub fn set_res(&mut self, res: OwnedHeap) {
        self.res = res;
    }

    pub fn is_owning_true(&self) -> bool {
        self.res == OwnedHeap::True
    }

    pub fn get_param(&self) -> bool {
        self.param
    }

    pub fn set_param(&mut self, p: bool) {
        self.param = p;
    }

    pub fn is_param_true(&self) -> bool {
        self.param == true
    }

    pub fn get_ptr(&self) -> bool {
        self.ptr
    }

    pub fn set_ptr(&mut self, p: bool) {
        self.ptr = p;
    }

    pub fn is_ptr_true(&self) -> bool {
        self.ptr == true
    }

    pub fn heap(&self) -> &'a OHAResultMap {
        self.ref_adt_heap
    }
}

#[derive(Clone)]
pub struct FindPtr<'tcx> {
    tcx: TyCtxt<'tcx>,
    unique: HashSet<DefId>,
    ptr: bool,
}

impl<'tcx> FindPtr<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            unique: HashSet::<DefId>::default(),
            ptr: false,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn unique(&self) -> &HashSet<DefId> {
        &self.unique
    }

    pub fn unique_mut(&mut self) -> &mut HashSet<DefId> {
        &mut self.unique
    }

    pub fn has_ptr(&self) -> bool {
        self.ptr
    }

    pub fn set_ptr(&mut self, ptr: bool) {
        self.ptr = ptr;
    }
}

pub fn is_display_verbose() -> bool {
    match env::var_os("ADT_DISPLAY") {
        Some(_) => true,
        _ => false,
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Default)]
pub struct IndexedTy<'tcx>(pub Option<(usize, &'tcx TyKind<'tcx>, Option<usize>, bool)>);

impl<'tcx> IndexedTy<'tcx> {
    pub fn new(ty: Ty<'tcx>, vidx: Option<VariantIdx>) -> Self {
        match &ty.kind() {
            TyKind::Tuple(list) => IndexedTy(Some((list.len(), &ty.kind(), None, true))),
            TyKind::Adt(adtdef, ..) => {
                if adtdef.is_enum() {
                    if vidx.is_none() {
                        return IndexedTy(None);
                    }
                    let idx = vidx.unwrap();
                    let len = adtdef.variants()[idx].fields.len();
                    IndexedTy(Some((len, &ty.kind(), Some(idx.index()), true)))
                } else {
                    let len = adtdef.variants()[VariantIdx::from_usize(0)].fields.len();
                    IndexedTy(Some((len, &ty.kind(), None, true)))
                }
            }
            TyKind::Array(..) | TyKind::Param(..) | TyKind::RawPtr(..) | TyKind::Ref(..) => {
                IndexedTy(Some((1, &ty.kind(), None, true)))
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(..)
            | TyKind::Uint(..)
            | TyKind::Float(..)
            | TyKind::Str
            | TyKind::Slice(..) => IndexedTy(Some((1, &ty.kind(), None, false))),
            _ => IndexedTy(None),
        }
    }

    // 0->unsupported, 1->trivial, 2-> needed
    pub fn get_priority(&self) -> usize {
        if self.0.is_none() {
            return 0;
        }
        match self.0.unwrap().0 {
            0 => 1,
            _ => match self.0.unwrap().3 {
                true => 2,
                false => 1,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct OwnershipLayoutResult {
    layout: Vec<OwnedHeap>,
    param: bool,
    requirement: bool,
    owned: bool,
}

impl OwnershipLayoutResult {
    pub fn new() -> Self {
        Self {
            layout: Vec::new(),
            param: false,
            requirement: false,
            owned: false,
        }
    }

    pub fn layout(&self) -> &Vec<OwnedHeap> {
        &self.layout
    }

    pub fn layout_mut(&mut self) -> &mut Vec<OwnedHeap> {
        &mut self.layout
    }

    pub fn get_param(&self) -> bool {
        self.param
    }

    pub fn set_param(&mut self, p: bool) {
        self.param = p;
    }

    pub fn is_param_true(&self) -> bool {
        self.param == true
    }

    pub fn get_requirement(&self) -> bool {
        self.requirement
    }

    pub fn set_requirement(&mut self, r: bool) {
        self.requirement = r;
    }

    pub fn is_requirement_true(&self) -> bool {
        self.requirement == true
    }

    pub fn is_empty(&self) -> bool {
        self.layout.is_empty()
    }

    pub fn is_owned(&self) -> bool {
        self.owned == true
    }

    pub fn set_owned(&mut self, o: bool) {
        self.owned = o;
    }

    pub fn update_from_default_heap_visitor<'tcx, 'a>(
        &mut self,
        default_heap: &mut DefaultOwnership<'tcx, 'a>,
    ) {
        if default_heap.is_owning_true() || default_heap.is_ptr_true() {
            self.set_requirement(true);
        }

        if default_heap.is_owning_true() {
            self.set_owned(true);
        }

        self.layout_mut().push(default_heap.get_res());

        self.set_param(default_heap.get_param());
    }
}
