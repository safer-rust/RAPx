//! User-facing rendering of contract data structures.
//!
//! Converts `ContractPlace`, `ContractExpr`, `NumericPredicate`, `PropertyArg`
//! and `Property` into readable strings for reports and debug output.  Kept
//! separate from the data model (`types.rs`) so the model stays
//! presentation-free.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use super::types::{
    ContractExpr, ContractPlace, ContractProjection, NumericOp, NumericPredicate,
    NumericUnaryOp, PlaceBase, Property, PropertyArg, PropertyKind, RelOp,
};

impl<'tcx> ContractPlace<'tcx> {
    pub fn display_user_friendly(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        let has_projections = !self.projections.is_empty();

        let base_str = match self.base {
            PlaceBase::Return => {
                if has_projections {
                    String::new()
                } else {
                    "return".to_string()
                }
            }
            PlaceBase::Arg(idx) => {
                if let Some(fn_def_id) = fn_def_id
                    && tcx.is_mir_available(fn_def_id)
                {
                    let mir_local = idx + 1;
                    let body = tcx.optimized_mir(fn_def_id);
                    if mir_local < body.local_decls.len() {
                        let local = rustc_middle::mir::Local::from_usize(mir_local);
                        let span = body.local_decls[local].source_info.span;
                        if let Ok(snippet) = tcx.sess.source_map().span_to_snippet(span)
                            && !snippet.is_empty()
                        {
                            return snippet;
                        }
                    }
                }
                format!("arg{}", idx)
            }
            PlaceBase::Local(n) => {
                if n == 0 {
                    "return".to_string()
                } else if let Some(fn_def_id) = fn_def_id
                    && tcx.is_mir_available(fn_def_id)
                {
                    let body = tcx.optimized_mir(fn_def_id);
                    if n < body.local_decls.len() {
                        let local = rustc_middle::mir::Local::from_usize(n);
                        let span = body.local_decls[local].source_info.span;
                        if let Ok(snippet) = tcx.sess.source_map().span_to_snippet(span) {
                            snippet
                        } else {
                            format!("arg{}", n)
                        }
                    } else {
                        format!("arg{}", n)
                    }
                } else {
                    format!("arg{}", n)
                }
            }
        };

        let base_str = base_str
            .strip_prefix("&mut ")
            .unwrap_or(&base_str)
            .to_string();
        let base_str = base_str.strip_prefix("&").unwrap_or(&base_str).to_string();

        if self.projections.is_empty() {
            return base_str;
        }

        let mut result = base_str;
        for projection in &self.projections {
            match projection {
                ContractProjection::Field { index, ty: _ } => {
                    let field_name =
                        crate::helpers::name::resolve_field_name(tcx, index, struct_def_id);
                    if result.is_empty() {
                        result = field_name;
                    } else {
                        result.push_str(&format!(".{}", field_name));
                    }
                }
                ContractProjection::Downcast { .. } => {
                    result.push_str(".unwrap_some()");
                }
                ContractProjection::IterElements => {
                    result.push_str(".iter()");
                }
            }
        }
        result
    }
}

impl<'tcx> NumericPredicate<'tcx> {
    pub fn display_user_friendly(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        let op_str = match self.op {
            RelOp::Eq => "==",
            RelOp::Ne => "!=",
            RelOp::Lt => "<",
            RelOp::Le => "<=",
            RelOp::Gt => ">",
            RelOp::Ge => ">=",
        };
        format!(
            "{} {} {}",
            display_expr_user_friendly(&self.lhs, tcx, struct_def_id, fn_def_id),
            op_str,
            display_expr_user_friendly(&self.rhs, tcx, struct_def_id, fn_def_id),
        )
    }
}

pub fn display_expr_user_friendly<'tcx>(
    expr: &ContractExpr<'tcx>,
    tcx: TyCtxt<'tcx>,
    struct_def_id: Option<DefId>,
    fn_def_id: Option<DefId>,
) -> String {
    match expr {
        ContractExpr::Const(n) => format!("{n}"),
        ContractExpr::ConstParam { name, .. } => name.clone(),
        ContractExpr::Place(p) => p.display_user_friendly(tcx, struct_def_id, fn_def_id),
        ContractExpr::SizeOf(ty) => format!("size_of({ty})"),
        ContractExpr::AlignOf(ty) => format!("align_of({ty})"),
        ContractExpr::Len(e) => {
            format!(
                "len({})",
                display_expr_user_friendly(e, tcx, struct_def_id, fn_def_id)
            )
        }
        ContractExpr::IndexAccess { slice, index } => {
            format!(
                "index_access({}, {})",
                display_expr_user_friendly(slice, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(index, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Binary { op, lhs, rhs } => {
            let op_str = match op {
                NumericOp::Add => "+",
                NumericOp::Sub => "-",
                NumericOp::Mul => "*",
                NumericOp::Div => "/",
                NumericOp::Rem => "%",
                NumericOp::BitAnd => "&",
                NumericOp::BitOr => "|",
                NumericOp::BitXor => "^",
            };
            format!(
                "{} {} {}",
                display_expr_user_friendly(lhs, tcx, struct_def_id, fn_def_id),
                op_str,
                display_expr_user_friendly(rhs, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Unary { op, expr } => {
            let op_str = match op {
                NumericUnaryOp::Not => "!",
                NumericUnaryOp::Neg => "-",
            };
            format!(
                "{}{}",
                op_str,
                display_expr_user_friendly(expr, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Min { a, b } => {
            format!(
                "min({}, {})",
                display_expr_user_friendly(a, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(b, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Max { a, b } => {
            format!(
                "max({}, {})",
                display_expr_user_friendly(a, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(b, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            format!(
                "if {} {{ {} }} else {{ {} }}",
                cond.display_user_friendly(tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(then_expr, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(else_expr, tcx, struct_def_id, fn_def_id),
            )
        }
        _ => format!("{:?}", expr),
    }
}

impl<'tcx> PropertyArg<'tcx> {
    pub fn display_for_report(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        match self {
            PropertyArg::Ty(ty) => format!("{}", ty),
            PropertyArg::Expr(expr) => {
                display_expr_user_friendly(expr, tcx, struct_def_id, fn_def_id)
            }
            PropertyArg::Predicates(preds) => {
                let p: Vec<_> = preds
                    .iter()
                    .map(|pred| pred.display_user_friendly(tcx, struct_def_id, fn_def_id))
                    .collect();
                p.join(" && ")
            }
            PropertyArg::Ident(s) => s.clone(),
        }
    }
}

impl<'tcx> Property<'tcx> {
    pub fn display_for_report(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        // Compound `def` (e.g. `Ptr2Ref`, `Deref`, user `pred!`): show
        // it as a single `name(args)` entry instead of its underlying primitives.
        if let Some(origin) = self.origin() {
            return format!("{}({})", origin.name, origin.args.join(", "));
        }

        let kind_str = match self.kind() {
            Some(k) => format!("{k:?}"),
            None => "Or".to_string(),
        };

        if matches!(self.kind(), Some(PropertyKind::InBound))
            && matches!(
                self.args().first(),
                Some(PropertyArg::Expr(ContractExpr::IndexAccess { .. }))
            )
        {
            if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
                self.args().first()
            {
                let slice_str = display_expr_user_friendly(slice, tcx, struct_def_id, fn_def_id);
                let index_str = display_expr_user_friendly(index, tcx, struct_def_id, fn_def_id);
                return format!("{}({}, {})", kind_str, slice_str, index_str);
            }
        }

        if matches!(self.kind(), Some(PropertyKind::ValidNum))
            && let Some(PropertyArg::Predicates(preds)) = self.args().first()
        {
            let inner: Vec<String> = preds
                .iter()
                .map(|pred| pred.display_user_friendly(tcx, struct_def_id, fn_def_id))
                .collect();
            if inner.is_empty() {
                return format!("{}", kind_str);
            }
            return format!("{}({})", kind_str, inner.join(", "));
        }

        let args: Vec<String> = self
            .args()
            .iter()
            .map(|arg| arg.display_for_report(tcx, struct_def_id, fn_def_id))
            .collect();
        if args.is_empty() {
            kind_str
        } else {
            format!("{}({})", kind_str, args.join(", "))
        }
    }
}
