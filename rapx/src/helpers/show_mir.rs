use crate::compat::FxHashSet;
use crate::def_id::is_drop_fn;
use crate::helpers::draw_dot::render_dot_string;
use crate::helpers::name::get_cleaned_def_path_name;
use colorful::{Color, Colorful};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlockData, BasicBlocks, Body, LocalDecl, LocalDecls, Operand, Rvalue, Statement,
    StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::{self, TyCtxt, TyKind};

const NEXT_LINE: &str = "\n";
const PADDING: &str = "    ";
const EXPLAIN: &str = " @ ";

// This trait is a wrapper towards std::Display or std::Debug, and is to resolve orphan restrictions.
pub trait Display {
    fn display(&self) -> String;
}

impl<'tcx> Display for Terminator<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{}{:?}{}", PADDING, self.kind, self.kind.display());
        s
    }
}

impl<'tcx> Display for TerminatorKind<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += EXPLAIN;
        match &self {
            TerminatorKind::Goto { .. } => s += "Goto",
            TerminatorKind::SwitchInt { .. } => s += "SwitchInt",
            TerminatorKind::Return => s += "Return",
            TerminatorKind::Unreachable => s += "Unreachable",
            TerminatorKind::Drop { .. } => s += "Drop",
            TerminatorKind::Assert { .. } => s += "Assert",
            TerminatorKind::Yield { .. } => s += "Yield",
            TerminatorKind::FalseEdge { .. } => s += "FalseEdge",
            TerminatorKind::FalseUnwind { .. } => s += "FalseUnwind",
            TerminatorKind::InlineAsm { .. } => s += "InlineAsm",
            TerminatorKind::UnwindResume => s += "UnwindResume",
            TerminatorKind::UnwindTerminate(..) => s += "UnwindTerminate",
            TerminatorKind::CoroutineDrop => s += "CoroutineDrop",
            TerminatorKind::Call { func, .. } => match func {
                Operand::Constant(constant) => match constant.ty().kind() {
                    ty::FnDef(id, ..) => {
                        s += &format!("Call: FnDid: {}", id.index.as_usize()).as_str()
                    }
                    _ => (),
                },
                _ => (),
            },
            TerminatorKind::TailCall { .. } => todo!(),
        };
        s
    }
}

impl<'tcx> Display for Statement<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{}{:?}{}", PADDING, self.kind, self.kind.display());
        s
    }
}

impl<'tcx> Display for StatementKind<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += EXPLAIN;
        match &self {
            StatementKind::Assign(assign) => {
                s += &format!("{:?}={:?}{}", assign.0, assign.1, assign.1.display());
            }
            StatementKind::FakeRead(..) => s += "FakeRead",
            StatementKind::SetDiscriminant { .. } => s += "SetDiscriminant",
            StatementKind::StorageLive(..) => s += "StorageLive",
            StatementKind::StorageDead(..) => s += "StorageDead",
            #[cfg(not(rapx_rustc_ge_198))]
            StatementKind::Retag(..) => s += "Retag",
            StatementKind::AscribeUserType(..) => s += "AscribeUserType",
            StatementKind::Coverage(..) => s += "Coverage",
            StatementKind::Nop => s += "Nop",
            StatementKind::PlaceMention(..) => s += "PlaceMention",
            StatementKind::Intrinsic(..) => s += "Intrinsic",
            StatementKind::ConstEvalCounter => s += "ConstEvalCounter",
            _ => todo!(),
        }
        s
    }
}

impl<'tcx> Display for Rvalue<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += EXPLAIN;
        match self {
            Rvalue::Use(..) => s += "Use",
            Rvalue::Repeat(..) => s += "Repeat",
            Rvalue::Ref(..) => s += "Ref",
            Rvalue::ThreadLocalRef(..) => s += "ThreadLocalRef",
            Rvalue::Cast(..) => s += "Cast",
            Rvalue::BinaryOp(..) => s += "BinaryOp",
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::NullaryOp(..) => s += "NullaryOp",
            Rvalue::UnaryOp(..) => s += "UnaryOp",
            Rvalue::Discriminant(..) => s += "Discriminant",
            Rvalue::Aggregate(..) => s += "Aggregate",
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::ShallowInitBox(..) => s += "ShallowInitBox",
            Rvalue::CopyForDeref(..) => s += "CopyForDeref",
            Rvalue::RawPtr(_, _) => s += "RawPtr",
            _ => todo!(),
        }
        s
    }
}

impl<'tcx> Display for BasicBlocks<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        for (index, bb) in self.iter().enumerate() {
            s += &format!(
                "bb {} {{{}{}}}{}",
                index,
                NEXT_LINE,
                bb.display(),
                NEXT_LINE
            );
        }
        s
    }
}

impl<'tcx> Display for BasicBlockData<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("CleanUp: {}{}", self.is_cleanup, NEXT_LINE);
        for stmt in self.statements.iter() {
            s += &format!("{}{}", stmt.display(), NEXT_LINE);
        }
        s += &format!(
            "{}{}",
            self.terminator.clone().unwrap().display(),
            NEXT_LINE
        );
        s
    }
}

impl<'tcx> Display for LocalDecls<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        for (index, ld) in self.iter().enumerate() {
            s += &format!("_{}: {} {}", index, ld.display(), NEXT_LINE);
        }
        s
    }
}

impl<'tcx> Display for LocalDecl<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{}{}", EXPLAIN, self.ty.kind().display());
        s
    }
}

impl<'tcx> Display for Body<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &self.local_decls.display();
        s += &self.basic_blocks.display();
        s
    }
}

impl<'tcx> Display for TyKind<'tcx> {
    fn display(&self) -> String {
        let mut s = String::new();
        s += &format!("{:?}", self);
        s
    }
}

impl Display for DefId {
    fn display(&self) -> String {
        format!("{:?}", self)
    }
}

pub struct ShowMir<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

// #[inline(always)]
pub fn display_mir(did: DefId, body: &Body) {
    rap_info!("{}", did.display().color(Color::LightRed));
    rap_info!("{}", body.local_decls.display().color(Color::Green));
    rap_info!(
        "{}",
        body.basic_blocks.display().color(Color::LightGoldenrod2a)
    );
}

impl<'tcx> ShowMir<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn start(&mut self) {
        rap_info!("Show MIR");
        let mir_keys = self.tcx.mir_keys(());
        for each_mir in mir_keys {
            let def_id = each_mir.to_def_id();
            let body = self.tcx.instance_mir(ty::InstanceKind::Item(def_id));
            display_mir(def_id, body);
        }
    }

    pub fn start_generate_dot(&mut self) {
        rap_info!("Generate MIR DOT");
        std::process::Command::new("mkdir")
            .args(["MIR_dot_graph"])
            .output()
            .expect("Failed to create directory");

        let mir_keys = self.tcx.mir_keys(());
        for each_mir in mir_keys {
            let def_id = each_mir.to_def_id();
            let _ = generate_mir_cfg_dot(self.tcx, def_id, &Vec::new());
        }
    }
}

pub fn generate_mir_cfg_dot<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    alias_sets: &Vec<FxHashSet<usize>>,
) -> Result<(), std::io::Error> {
    let mir = tcx.optimized_mir(def_id);
    let mut dot_content = String::new();
    let alias_info_str = format!("Alias Sets: {:?}", alias_sets);

    dot_content.push_str(&format!(
        "digraph mir_cfg_{} {{\n",
        get_cleaned_def_path_name(tcx, def_id)
    ));
    dot_content.push_str(&format!(
        "    label = \"MIR CFG for {}\\n{}\\n\";\n",
        tcx.def_path_str(def_id),
        alias_info_str.replace("\"", "\\\"")
    ));
    dot_content.push_str("    labelloc = \"t\";\n");
    dot_content.push_str("    node [shape=box, fontname=\"Courier\", align=\"left\"];\n\n");

    for (bb_index, bb_data) in mir.basic_blocks.iter_enumerated() {
        let mut lines: Vec<String> = bb_data
            .statements
            .iter()
            .map(|stmt| format!("{:?}", stmt))
            .collect();
        let mut node_style = String::new();

        if let Some(terminator) = &bb_data.terminator {
            let mut is_drop_related = false;
            match &terminator.kind {
                TerminatorKind::Drop { .. } => is_drop_related = true,
                TerminatorKind::Call { func, .. } => {
                    if let Operand::Constant(c) = func
                        && let ty::FnDef(def_id, _) = *c.ty().kind()
                        && is_drop_fn(def_id)
                    {
                        is_drop_related = true;
                    }
                }
                _ => {}
            }
            if is_drop_related {
                node_style = ", style=\"filled\", fillcolor=\"#ffdddd\", color=\"red\"".to_string();
            }
            lines.push(format!("{:?}", terminator.kind));
        } else {
            lines.push("(no terminator)".to_string());
        }

        let label_content = lines.join("\\l");
        let node_label = format!("BB{}:\\l{}\\l", bb_index.index(), label_content);
        dot_content.push_str(&format!(
            "    BB{} [label=\"{}\"{}];\n",
            bb_index.index(),
            node_label.replace("\"", "\\\""),
            node_style
        ));

        if let Some(terminator) = &bb_data.terminator {
            for target in terminator.successors() {
                dot_content.push_str(&format!(
                    "    BB{} -> BB{} [label=\"\"];\n",
                    bb_index.index(),
                    target.index(),
                ));
            }
        }
    }
    dot_content.push_str("}\n");
    let name = get_cleaned_def_path_name(tcx, def_id);
    render_dot_string(name, dot_content);
    Ok(())
}
