use super::{UPGAnalysis, upg_graph::UPGraph};
use crate::analysis::utils::{
    draw_dot::{DotGraph, render_dot_graphs},
    fn_info::*,
    show_mir::display_mir,
};
use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::Local,
    ty,
    ty::{TyCtxt, Visibility},
};
use rustc_span::Symbol;
use std::collections::{HashMap, HashSet};

impl<'tcx> UPGAnalysis<'tcx> {
    pub fn audit_std_unsafe(&mut self) {
        let all_std_fn_def = get_all_std_fns_by_rustc_public(self.tcx);
        // Specific task for vec;
        let symbol = Symbol::intern("Vec");
        let vec_def_id = self.tcx.get_diagnostic_item(symbol).unwrap();
        for &def_id in &all_std_fn_def {
            let adt_def = get_adt_def_id_by_adt_method(self.tcx, def_id);
            if adt_def.is_some() && adt_def.unwrap() == vec_def_id {
                self.insert_upg(def_id);
            }
        }
        self.render_dot();
    }

    pub fn render_dot(&mut self) {
        let mut dots = Vec::new();
        for upg in &self.upgs {
            let dot_str = UPGraph::generate_dot_from_upg_unit(upg);
            let caller_name = get_cleaned_def_path_name(self.tcx, upg.caller.def_id);
            dots.push(DotGraph::new(caller_name, dot_str));
        }
        render_dot_graphs(&dots);
    }

    pub fn get_chains(&mut self) {
        let v_fn_def = self.tcx.mir_keys(());

        for local_def_id in v_fn_def {
            let def_id = local_def_id.to_def_id();
            if !check_visibility(self.tcx, def_id) {
                continue;
            }
            if get_cleaned_def_path_name(self.tcx, def_id) == "std::boxed::Box::<T>::from_raw" {
                let body = self.tcx.mir_built(local_def_id).steal();
                display_mir(def_id, &body);
            }
            let chains = get_all_std_unsafe_chains(self.tcx, def_id);
            let valid_chains: Vec<Vec<String>> = chains
                .into_iter()
                .filter(|chain| {
                    if chain.len() > 1 {
                        return true;
                    }
                    if chain.len() == 1 {
                        if check_safety(self.tcx, def_id) == Safety::Unsafe {
                            return true;
                        }
                    }
                    false
                })
                .collect();

            print_unsafe_chains(&valid_chains);
        }
    }

    pub fn get_all_std_unsafe_def_id_by_treat_std_as_local_crate(
        &mut self,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<DefId> {
        let mut unsafe_fn = HashSet::default();
        let mut total_cnt = 0;
        let mut api_cnt = 0;
        let mut sp_cnt = 0;
        let mut sp_count_map: HashMap<String, usize> = HashMap::new();
        let all_std_fn_def = get_all_std_fns_by_rustc_public(self.tcx);

        for def_id in &all_std_fn_def {
            if check_safety(tcx, *def_id) == Safety::Unsafe {
                let sp_set = get_sp(tcx, *def_id);
                if !sp_set.is_empty() {
                    unsafe_fn.insert(*def_id);
                    let mut flag = false;
                    for sp in &sp_set {
                        if sp.is_empty()
                            || sp == "Function_sp"
                            || sp == "System_sp"
                            || sp == "ValidSlice"
                        {
                            flag = true;
                        }
                    }
                    if !flag {
                        api_cnt += 1;
                        sp_cnt += sp_set.len();
                    }
                    total_cnt += 1;
                }
                for sp in sp_set {
                    *sp_count_map.entry(sp).or_insert(0) += 1;
                }
            }
            self.insert_upg(*def_id);
        }

        rap_info!(
            "fn_def : {}, count : {:?} and {:?}, sp cnt : {}",
            all_std_fn_def.len(),
            total_cnt,
            api_cnt,
            sp_cnt
        );
        unsafe_fn
    }

    pub fn check_params(&self, def_id: DefId) {
        let body = self.tcx.optimized_mir(def_id);
        let locals = body.local_decls.clone();
        let fn_sig = self.tcx.fn_sig(def_id).skip_binder();
        let param_len = fn_sig.inputs().skip_binder().len();
        let return_ty = fn_sig.output().skip_binder();
        for idx in 1..param_len + 1 {
            let local_ty = locals[Local::from(idx)].ty;
            if is_ptr(local_ty) && !return_ty.is_unit() {
                println!("{:?}", get_cleaned_def_path_name(self.tcx, def_id));
            }
        }
    }

    pub fn analyze_upg(&self) {
        let mut fn_no_callee = Vec::new();
        let mut fn_unsafe_caller = Vec::new();
        let mut fn_safe_caller = Vec::new();
        let mut method_no_callee = Vec::new();
        let mut method_unsafe_caller = Vec::new();
        let mut method_safe_caller = Vec::new();
        for upg in &self.upgs {
            if upg.caller.fn_kind == FnKind::Method {
                // method
                if upg.callees.is_empty() {
                    method_no_callee.push(upg.clone());
                }
                if upg.caller.fn_safety == Safety::Unsafe {
                    method_unsafe_caller.push(upg.clone());
                } else {
                    method_safe_caller.push(upg.clone());
                }
            } else {
                //function
                if upg.callees.is_empty() {
                    fn_no_callee.push(upg.clone());
                }
                if upg.caller.fn_safety == Safety::Unsafe {
                    fn_unsafe_caller.push(upg.clone());
                } else {
                    fn_safe_caller.push(upg.clone());
                }
            }
        }
        rap_info!(
            "func: {},{},{}, method: {},{},{}",
            fn_no_callee.len(),
            fn_unsafe_caller.len(),
            fn_safe_caller.len(),
            method_no_callee.len(),
            method_unsafe_caller.len(),
            method_safe_caller.len()
        );
        rap_info!("units: {}", self.upgs.len());
    }

    pub fn analyze_struct(&self) {
        let mut cache = HashSet::default();
        let mut s = 0;
        let mut u = 0;
        let mut e = 0;
        let mut uc = 0;
        let mut vi = 0;
        for upg in &self.upgs {
            self.get_struct(
                upg.caller.def_id,
                &mut cache,
                &mut s,
                &mut u,
                &mut e,
                &mut uc,
                &mut vi,
            );
        }
        println!("{},{},{},{}", s, u, e, vi);
    }

    pub fn get_struct(
        &self,
        def_id: DefId,
        cache: &mut HashSet<DefId>,
        s: &mut usize,
        u: &mut usize,
        e: &mut usize,
        uc: &mut usize,
        vi: &mut usize,
    ) {
        let tcx = self.tcx;
        let mut safe_constructors = Vec::new();
        let mut unsafe_constructors = Vec::new();
        let mut unsafe_methods = Vec::new();
        let mut safe_methods = Vec::new();
        let mut mut_methods = Vec::new();
        let mut struct_name = "".to_string();
        let mut ty_flag = 0;
        let mut vi_flag = false;
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    if adt_def.is_union() {
                        ty_flag = 1;
                    } else if adt_def.is_enum() {
                        ty_flag = 2;
                    }
                    let adt_def_id = adt_def.did();
                    struct_name = get_cleaned_def_path_name(tcx, adt_def_id);
                    if !cache.insert(adt_def_id) {
                        return;
                    }

                    vi_flag = false;
                    let impl_vec = get_impls_for_struct(self.tcx, adt_def_id);
                    for impl_id in impl_vec {
                        let associated_items = tcx.associated_items(impl_id);
                        for item in associated_items.in_definition_order() {
                            if let ty::AssocKind::Fn {
                                name: _,
                                has_self: _,
                            } = item.kind
                            {
                                let item_def_id = item.def_id;
                                if !get_sp(self.tcx, item_def_id).is_empty() {
                                    vi_flag = true;
                                }
                                if get_type(self.tcx, item_def_id) == FnKind::Constructor
                                    && check_safety(self.tcx, item_def_id) == Safety::Unsafe
                                // && get_sp(self.tcx, item_def_id).len() > 0
                                {
                                    unsafe_constructors.push(item_def_id);
                                }
                                if get_type(self.tcx, item_def_id) == FnKind::Constructor
                                    && check_safety(self.tcx, item_def_id) == Safety::Safe
                                {
                                    safe_constructors.push(item_def_id);
                                }
                                if get_type(self.tcx, item_def_id) == FnKind::Method
                                    && check_safety(self.tcx, item_def_id) == Safety::Unsafe
                                // && get_sp(self.tcx, item_def_id).len() > 0
                                {
                                    unsafe_methods.push(item_def_id);
                                }
                                if get_type(self.tcx, item_def_id) == FnKind::Method
                                    && check_safety(self.tcx, item_def_id) == Safety::Safe
                                {
                                    if !get_unsafe_callees(tcx, item_def_id).is_empty() {
                                        safe_methods.push(item_def_id);
                                    }
                                }
                                if get_type(self.tcx, item_def_id) == FnKind::Method
                                    && has_mut_self_param(self.tcx, item_def_id)
                                {
                                    mut_methods.push(item_def_id);
                                }
                            }
                        }
                    }
                }
            }
        }
        if struct_name == *""
            || (unsafe_constructors.is_empty()
                && unsafe_methods.is_empty()
                && safe_methods.is_empty())
        {
            return;
        }
        if vi_flag {
            *vi += 1;
        }
        if !unsafe_constructors.is_empty() {
            *uc += 1;
        }
        if ty_flag == 0 {
            *s += 1;
        }
        if ty_flag == 1 {
            *u += 1;
        }
        if ty_flag == 2 {
            *e += 1;
        }

        println!("Safe Cons: {}", safe_constructors.len());
        for safe_cons in safe_constructors {
            println!(" {:?}", get_cleaned_def_path_name(tcx, safe_cons));
        }
        println!("Unsafe Cons: {}", unsafe_constructors.len());
        for unsafe_cons in unsafe_constructors {
            println!(" {:?}", get_cleaned_def_path_name(tcx, unsafe_cons));
        }
        println!("Unsafe Methods: {}", unsafe_methods.len());
        for method in unsafe_methods {
            println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        }
        println!("Safe Methods with unsafe callee: {}", safe_methods.len());
        for method in safe_methods {
            println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        }
        println!("Mut self Methods: {}", mut_methods.len());
        for method in mut_methods {
            println!(" {:?}", get_cleaned_def_path_name(tcx, method));
        }
    }

    pub fn get_units_data(&mut self, tcx: TyCtxt<'tcx>) {
        // [uf/um, sf-uf, sf-um, uf-uf, uf-um, um(sf)-uf, um(uf)-uf, um(sf)-um, um(uf)-um, sm(sf)-uf, sm(uf)-uf, sm(sf)-um, sm(uf)-um]
        let mut basic_units_data = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let def_id_sets = tcx.mir_keys(());
        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                self.insert_upg(def_id);
            }
        }
        for upg in &self.upgs {
            upg.count_basic_units(&mut basic_units_data);
        }
    }

    pub fn process_def_id(
        &mut self,
        def_id: DefId,
        visited: &mut HashSet<DefId>,
        unsafe_fn: &mut HashSet<DefId>,
    ) {
        if !visited.insert(def_id) {
            return;
        }
        match self.tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                if check_safety(self.tcx, def_id) == Safety::Unsafe
                    && self.tcx.visibility(def_id) == Visibility::Public
                {
                    unsafe_fn.insert(def_id);
                    self.insert_upg(def_id);
                }
            }
            DefKind::Mod => {
                for child in self.tcx.module_children(def_id) {
                    if let Some(child_def_id) = child.res.opt_def_id() {
                        self.process_def_id(child_def_id, visited, unsafe_fn);
                    }
                }
            }
            DefKind::Impl { of_trait: _ } => {
                for item in self.tcx.associated_item_def_ids(def_id) {
                    self.process_def_id(*item, visited, unsafe_fn);
                }
            }
            DefKind::Struct => {
                let impls = self.tcx.inherent_impls(def_id);
                for impl_def_id in impls {
                    self.process_def_id(*impl_def_id, visited, unsafe_fn);
                }
            }
            DefKind::Ctor(_of, _kind) => {
                if self.tcx.is_mir_available(def_id) {
                    let _mir = self.tcx.optimized_mir(def_id);
                }
            }
            _ => {
                // println!("{:?}",tcx.def_kind(def_id));
            }
        }
    }
}
