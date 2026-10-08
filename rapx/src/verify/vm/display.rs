//! Debug and diagnostic display for the symbolic VM.

use std::fmt;

use super::state::ValueFacts;

impl fmt::Display for ValueFacts<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut flags = Vec::new();
        if self.non_null {
            flags.push("non_null");
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
