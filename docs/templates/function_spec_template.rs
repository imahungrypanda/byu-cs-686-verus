// Verus Function Spec Template
// Reference: https://verus-lang.github.io/verus/guide/overview.html

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Replace the function name and types as needed
    pub exec fn example(x: u64) -> (y: u64)
        requires
            // preconditions here, e.g., x < 100
        ensures
            // postconditions here, e.g., y >= x
    {
        // implementation here
        x
    }
}
