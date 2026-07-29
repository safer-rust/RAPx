pub mod debug;
pub mod graph;
pub mod solver;

use crate::analysis::range_analysis::domain::domain::*;
use crate::analysis::range_analysis::Range;

use crate::analysis::range_analysis::domain::symbolic_expr::*;
use crate::analysis::path_analysis::PathTree;
use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::*,
    ty::{self, TyCtxt},
};

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
};

#[derive(Clone)]

pub struct ConstraintGraph<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub tcx: TyCtxt<'tcx>,
    pub body: &'tcx Body<'tcx>,
    // Protected fields
    pub self_def_id: DefId,      // The DefId of the function being analyzed
    pub vars: VarNodes<'tcx, T>, // The variables of the source program

    pub oprs: Vec<BasicOpKind<'tcx, T>>, // The operations of the source program

    pub defmap: DefMap<'tcx>, // Map from variables to the operations that define them
    pub usemap: UseMap<'tcx>, // Map from variables to operations where variables are used
    pub symbmap: SymbMap<'tcx>, // Map from variables to operations where they appear as bounds
    pub values_branchmap: HashMap<&'tcx Place<'tcx>, ValueBranchMap<'tcx, T>>, // Store intervals, basic blocks, and branches
    constant_vector: Vec<T>, // Vector for constants from an SCC

    pub essa: DefId,
    pub ssa: DefId,
    pub index: i32,
    pub dfs: HashMap<&'tcx Place<'tcx>, i32>,
    pub root: HashMap<&'tcx Place<'tcx>, &'tcx Place<'tcx>>,
    pub in_component: HashSet<&'tcx Place<'tcx>>,
    pub components: HashMap<&'tcx Place<'tcx>, HashSet<&'tcx Place<'tcx>>>,
    pub worklist: VecDeque<&'tcx Place<'tcx>>,
    pub numAloneSCCs: usize,
    pub numSCCs: usize, // Add a stub for pre_update to resolve the missing method error.
    pub final_vars: VarNodes<'tcx, T>,
    pub rerurn_places: HashSet<&'tcx Place<'tcx>>,
    pub switchbbs: HashMap<BasicBlock, (Place<'tcx>, Place<'tcx>)>,
    pub const_func_place: HashMap<&'tcx Place<'tcx>, usize>,
    pub unique_adt_path: HashMap<String, usize>,
}



impl<'tcx, T> ConstraintGraph<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn convert_const(c: &Const) -> Option<T> {
        T::from_const(c)
    }

    pub fn new(
        body: &'tcx Body<'tcx>,
        tcx: TyCtxt<'tcx>,
        self_def_id: DefId,
        essa: DefId,
        ssa: DefId,
    ) -> Self {
        let mut unique_adt_path: HashMap<String, usize> = HashMap::new();
        unique_adt_path.insert("std::ops::Range".to_string(), 1);

        Self {
            tcx,
            body,
            self_def_id,
            vars: VarNodes::new(),
            oprs: GenOprs::new(),
            defmap: DefMap::new(),
            usemap: UseMap::new(),
            symbmap: SymbMap::new(),
            values_branchmap: ValuesBranchMap::new(),
            constant_vector: Vec::new(),
            essa,
            ssa,
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: VecDeque::new(),
            numAloneSCCs: 0,
            numSCCs: 0,
            final_vars: VarNodes::new(),
            rerurn_places: HashSet::new(),
            switchbbs: HashMap::new(),
            const_func_place: HashMap::new(),
            unique_adt_path: unique_adt_path,
        }
    }

    pub fn new_without_ssa(body: &'tcx Body<'tcx>, tcx: TyCtxt<'tcx>, self_def_id: DefId) -> Self {
        let mut unique_adt_path: HashMap<String, usize> = HashMap::new();
        unique_adt_path.insert("std::ops::Range".to_string(), 1);
        Self {
            tcx,
            body,
            self_def_id,
            vars: VarNodes::new(),

            oprs: GenOprs::new(),
            defmap: DefMap::new(),
            usemap: UseMap::new(),
            symbmap: SymbMap::new(),
            values_branchmap: ValuesBranchMap::new(),
            constant_vector: Vec::new(),
            essa: self_def_id, // Assuming essa is the same as self_def_id
            ssa: self_def_id,  // Assuming ssa is the same as self_def_id
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: VecDeque::new(),
            numAloneSCCs: 0,
            numSCCs: 0,
            final_vars: VarNodes::new(),
            rerurn_places: HashSet::new(),
            switchbbs: HashMap::new(),
            const_func_place: HashMap::new(),
            unique_adt_path: unique_adt_path,
        }
    }

    pub fn build_final_vars(
        &mut self,
        places_map: &HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
    ) -> (VarNodes<'tcx, T>, Vec<Place<'tcx>>) {
        let mut final_vars: VarNodes<'tcx, T> = HashMap::new();
        let mut not_found: Vec<Place<'tcx>> = Vec::new();

        for (&_key_place, place_set) in places_map {
            for &place in place_set {
                let found = self.vars.iter().find(|&(&p, _)| *p == place);

                if let Some((&found_place, var_node)) = found {
                    final_vars.insert(found_place, var_node.clone());
                } else {
                    not_found.push(place);
                }
            }
        }
        self.final_vars = final_vars.clone();
        (final_vars, not_found)
    }

    pub fn filter_final_vars(
        vars: &VarNodes<'tcx, T>,
        places_map: &HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
    ) -> HashMap<Place<'tcx>, Range<T>> {
        let mut final_vars = HashMap::new();

        for (&_key_place, place_set) in places_map {
            for &place in place_set {
                if let Some(var_node) = vars.get(&place) {
                    final_vars.insert(place, var_node.get_range().clone());
                }
            }
        }
        final_vars
    }

    pub fn get_vars(&self) -> &VarNodes<'tcx, T> {
        &self.vars
    }

    pub fn get_field_place(&self, adt_place: Place<'tcx>, field_index: FieldIdx) -> Place<'tcx> {
        let adt_ty = adt_place.ty(&self.body.local_decls, self.tcx).ty;
        let field_ty = match adt_ty.kind() {
            ty::TyKind::Adt(adt_def, substs) => {
                // Get the single variant of the struct using an iterator.
                let variant_def = adt_def.variants().iter().next().unwrap();

                // Get the field's definition from the variant.
                let field_def = &variant_def.fields[field_index];

                // Return the field's type as the result of this match arm.
                // (The "let field_ty =" is removed from this line)
                #[cfg(not(rapx_rustc_ge_198))]
                let ft = field_def.ty(self.tcx, substs);
                #[cfg(rapx_rustc_ge_198)]
                let ft = field_def.ty(self.tcx, substs).skip_norm_wip();
                ft
            }
            _ => {
                panic!("get_field_place expected an ADT, but found {:?}", adt_ty);
            }
        };

        let mut new_projection = adt_place.projection.to_vec();
        new_projection.push(ProjectionElem::Field(field_index, field_ty));

        let new_place = Place {
            local: adt_place.local,
            projection: self.tcx.mk_place_elems(&new_projection),
        };
        new_place
    }

    pub fn start_analyze_path_constraints(
        &mut self,
        body: &'tcx Body<'tcx>,
        tree: &PathTree,
    ) -> HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> {
        self.build_value_maps(body);
        let result = self.analyze_path_constraints(body, tree);
        result
    }

    pub fn analyze_path_constraints(
        &self,
        body: &'tcx Body<'tcx>,
        tree: &PathTree,
    ) -> HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> {
        let mut all_path_results: HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> =
            HashMap::with_capacity(tree.len());

        for path_indices in tree.iter() {
            let mut current_path_constraints: Vec<(Place<'tcx>, Place<'tcx>, BinOp)> = Vec::new();

            let path_bbs: Vec<BasicBlock> = path_indices
                .iter()
                .map(|&idx| BasicBlock::from_usize(idx))
                .collect();

            for window in path_bbs.windows(2) {
                let current_bb = window[0];

                if self.switchbbs.contains_key(&current_bb) {
                    let next_bb = window[1];
                    let current_bb_data = &body[current_bb];

                    if let Some(Terminator {
                        kind: TerminatorKind::SwitchInt { discr, .. },
                        ..
                    }) = &current_bb_data.terminator
                    {
                        let (constraint_place_1, constraint_place_2) =
                            self.switchbbs.get(&current_bb).unwrap();
                        if let Some(vbm) = self.values_branchmap.get(constraint_place_1) {
                            let relevant_interval_opt = if next_bb == *vbm.get_bb_true() {
                                Some(vbm.get_itv_t())
                            } else if next_bb == *vbm.get_bb_false() {
                                Some(vbm.get_itv_f())
                            } else {
                                None
                            };

                            if let Some(relevant_interval) = relevant_interval_opt {
                                match relevant_interval {
                                    IntervalType::Basic(basic_interval) => {}
                                    IntervalType::Symb(symb_interval) => {
                                        current_path_constraints.push((
                                            constraint_place_1.clone(),
                                            constraint_place_2.clone(),
                                            symb_interval.get_operation().clone(),
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            }

            all_path_results.insert(path_indices, current_path_constraints);
        }

        all_path_results
    }
}
