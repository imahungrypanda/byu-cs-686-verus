// Verus Quantifier Proof Template
// Reference: https://verus-lang.github.io/verus/guide/overview.html

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    pub proof fn lemma_all_nonneg(a: Seq<int>)
        requires
            // e.g., forall |i: int| 0 <= i < a.len() ==> a[i] >= 0
        ensures
            // desired quantified property
    {
        assert forall |i: int| 0 <= i < a.len() ==> a[i] >= 0 by {
            // trigger guidance / local reasoning here
        };
    }
}
