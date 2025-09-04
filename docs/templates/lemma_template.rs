// Verus Lemma / Proof Template
// Reference: https://verus-lang.github.io/verus/guide/overview.html

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Replace lemma name and statements
    pub proof fn lemma_example(x: int)
        requires
            // assumptions about x
        ensures
            // desired property of x
    {
        // proof steps
        // assert ... by { ... }
    }
}
