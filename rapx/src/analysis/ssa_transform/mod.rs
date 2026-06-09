#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]

pub mod Replacer;
pub mod SSATransformer;

use crate::{rap_info, rap_warn};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::{
        pretty::{self, MirWriter, PrettyPrintMirOptions},
        *,
    },
    ty::TyCtxt,
};
use std::{
    collections::{HashMap, HashSet},
    fs::{self, File},
    io::{self, Cursor, Write},
    path::PathBuf,
};

pub struct SSATrans<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub debug: bool,
}

impl<'tcx> SSATrans<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, debug: bool) -> Self {
        Self { tcx: tcx, debug }
    }

    pub fn start(&mut self) {
        for local_def_id in self.tcx.iter_local_def_id() {
            if matches!(self.tcx.def_kind(local_def_id), DefKind::Fn) {
                if self.tcx.hir_maybe_body_owned_by(local_def_id).is_some() {
                    if let Some(def_id) = self
                        .tcx
                        .hir_body_owners()
                        .find(|id| self.tcx.def_path_str(*id) == "main")
                    {
                        if let Some(ssa_def_id) =
                            self.tcx.hir_crate_items(()).free_items().find(|id| {
                                let hir_id = id.hir_id();
                                if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                    ident_name.to_string() == "SSAstmt"
                                } else {
                                    false
                                }
                            })
                        {
                            let ssa_def_id = ssa_def_id.owner_id.to_def_id();
                            if let Some(essa_def_id) =
                                self.tcx.hir_crate_items(()).free_items().find(|id| {
                                    let hir_id = id.hir_id();
                                    if let Some(ident_name) = self.tcx.hir_opt_name(hir_id) {
                                        ident_name.to_string() == "ESSAstmt"
                                    } else {
                                        false
                                    }
                                })
                            {
                                let essa_def_id = essa_def_id.owner_id.to_def_id();
                                self.analyze_mir(self.tcx, def_id, ssa_def_id, essa_def_id);
                            }
                        }
                    }
                }
            }
        }
    }
    fn analyze_mir(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: LocalDefId,
        ssa_def_id: DefId,
        essa_def_id: DefId,
    ) {
        let mut body = tcx.optimized_mir(def_id).clone();
        {
            let body_mut_ref: &mut Body<'tcx> = unsafe { &mut *(&mut body as *mut Body<'tcx>) };
            let mut passrunner = PassRunner::new(tcx);
            passrunner.run_pass(body_mut_ref, ssa_def_id, essa_def_id);
            // passrunner.print_diff(body_mut_ref);
            let essa_mir_string = passrunner.get_final_ssa_as_string(body_mut_ref);
            // rap_info!("final SSA {:?}\n", &essa_mir_string);
            rap_info!("ssa lvalue check {:?}", lvalue_check(&essa_mir_string));
        }
    }
}
pub struct PassRunner<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub places_map: HashMap<Place<'tcx>, HashSet<Place<'tcx>>>,
}
pub fn lvalue_check(mir_string: &str) -> bool {
    let re = regex::Regex::new(r"_(\d+)\s*=").unwrap();
    let mut counts = HashMap::new();
    let mut has_duplicate = false;

    for cap in re.captures_iter(mir_string) {
        let var = cap[1].parse::<u32>().unwrap();
        let counter = counts.entry(var).or_insert(0);
        *counter += 1;
        if *counter > 1 {
            has_duplicate = true;
        }
    }

    for (var, count) in counts {
        if count > 1 {
            rap_warn!("Variable _ {} is used {} times", var, count);
        }
    }

    !has_duplicate
}
pub fn print_diff<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, def_id: DefId) {
    let dir_path = "ssa_mir";
    fs::create_dir_all(dir_path).unwrap();
    // PassRunner::new(self.tcx);
    let name = tcx.def_path_str(def_id);
    let mir_file_path = format!("{}/origin_mir.txt", dir_path);
    let phi_mir_file_path = format!("{}/{}_after_rename_mir.txt", dir_path, name);
    let mut file = File::create(&mir_file_path).unwrap();
    let mut w = io::BufWriter::new(&mut file);
    write_mir_pretty(tcx, None, &mut w).unwrap();
    let mut file2 = File::create(&phi_mir_file_path).unwrap();
    let mut w2 = io::BufWriter::new(&mut file2);
    let writer = pretty::MirWriter::new(tcx);
    writer.write_mir_fn(body, &mut w2).unwrap();
}
pub fn print_mir_graph<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, def_id: DefId) {
    let dir_path = PathBuf::from("passrunner_mir_dot");
    fs::create_dir_all(dir_path.clone()).unwrap();

    let dot_graph = mir_to_dot(tcx, body);
    let function_name = tcx.def_path_str(def_id);
    let safe_filename = format!("{}_after_rename_mir.dot", function_name);
    let output_path = dir_path.join(format!("{}", safe_filename));

    let mut file = File::create(&output_path).expect("cannot create file");
    let _ = file.write_all(dot_graph.as_bytes());
}
//for f in *.dot; do dot -Tpng "$f" -o "${f%.dot}.png"; done
fn mir_to_dot<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> String {
    let mut dot = String::new();
    dot.push_str("digraph MIR {\n");
    dot.push_str("  node [shape=box];\n");

    for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let statements_str = bb_data
            .statements
            .iter()
            .filter(|stmt| {
                !matches!(
                    stmt.kind,
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_)
                )
            })
            .map(|stmt| format!("{:?}", stmt).replace('\n', " "))
            .collect::<Vec<_>>()
            .join("\\l");

        let terminator_str = match &bb_data.terminator {
            Some(term) => match term.kind {
                TerminatorKind::Assert { .. } => String::new(),
                _ => format!("{:?}", term.kind).replace("->", "-->"),
            },
            None => "NoTerminator".to_string(),
        };

        let label = format!("{}\\l{}\\l", statements_str, terminator_str);

        dot.push_str(&format!(
            "  {} [label=\"{:?}:\\l{}\"];\n",
            bb.index(),
            bb,
            label
        ));

        if let Some(terminator) = &bb_data.terminator {
            for successor in terminator.successors() {
                dot.push_str(&format!("  {} -> {};\n", bb.index(), successor.index()));
            }
        }
    }

    dot.push_str("}\n");
    dot
}

impl<'tcx> PassRunner<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            places_map: HashMap::default(),
        }
    }

    pub fn get_final_ssa_as_string(&self, body: &Body<'tcx>) -> String {
        let mut buffer2 = Cursor::new(Vec::new());
        let writer = pretty::MirWriter::new(self.tcx);
        writer.write_mir_fn(body, &mut buffer2).unwrap();
        let after_mir = String::from_utf8(buffer2.into_inner()).unwrap();
        after_mir
    }

    pub fn run_pass(&mut self, body: &mut Body<'tcx>, ssa_def_id: DefId, essa_def_id: DefId) {
        let arg_count = body.arg_count;
        let ssatransformer =
            SSATransformer::SSATransformer::new(self.tcx, body, ssa_def_id, essa_def_id, arg_count);
        let mut replacer = Replacer::Replacer {
            tcx: self.tcx,
            ssatransformer,
            new_local_collection: HashSet::default(),
            new_locals_to_declare: HashMap::default(),
        };
        replacer.insert_phi_statment(body);
        replacer.insert_essa_statement(body);
        replacer.rename_variables(body);
        self.places_map = replacer.ssatransformer.places_map.clone();
    }
}
