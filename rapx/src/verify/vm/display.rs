//! Debug and diagnostic display for the symbolic VM.

use std::fmt;

use super::state::ValueInvariants;

impl fmt::Display for ValueInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut flags = Vec::new();
        if self.non_null {
            flags.push("non_null");
        }
        if self.aligned {
            flags.push("aligned");
        }
        if self.init {
            flags.push("init");
        }
        if self.in_bounds {
            flags.push("in_bounds");
        }
        write!(f, "{}", flags.join("|"))
    }
}
