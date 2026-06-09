use rustc_middle::ty::{self, Mutability, Ty};
use serde::Serialize;
use std::{fmt::Display, sync::OnceLock};

use super::transform::TransformKind;

#[derive(Clone, Copy, Eq, PartialEq, Debug, Serialize)]
#[serde(tag = "type")]
pub enum DepEdge {
    Arg { no: usize },
    Ret,
    Transform(TransformKind),
}

impl Display for DepEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DepEdge::Arg { no } => write!(f, "{}", no),
            DepEdge::Ret => write!(f, "r"),
            DepEdge::Transform(kind) => write!(f, "Transform({})", kind),
        }
    }
}

impl DepEdge {
    pub fn arg(no: usize) -> DepEdge {
        DepEdge::Arg { no }
    }
    pub fn ret() -> DepEdge {
        DepEdge::Ret
    }

    pub fn transform(kind: TransformKind) -> DepEdge {
        DepEdge::Transform(kind)
    }
    pub fn as_transform_kind(self) -> Option<TransformKind> {
        match self {
            DepEdge::Transform(kind) => Some(kind),
            _ => None,
        }
    }
}
