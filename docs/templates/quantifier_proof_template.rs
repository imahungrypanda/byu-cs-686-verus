// Verus Quantifier Proof Template
// Reference: https://verus-lang.github.io/verus/guide/overview.html
// Triggers guide: https://verus-lang.github.io/verus/guide/forall.html?highlight=trigger#forall-and-triggers

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Cheat sheet: triggers for forall / exists
    // - Mark trigger terms with #[trigger]
    // - A valid trigger must be a term (function/field/index) that mentions all bound vars
    // - Good patterns with Seq: #[trigger] s[i], #[trigger] s.len()
    // - Avoid triggers like (0 <= i); use a helper spec fn if needed
    // - You can accept auto-chosen triggers with #![auto]

    pub proof fn lemma_all_nonneg(a: Seq<int>)
        requires
            // e.g., forall |i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0
        ensures
            // desired quantified property
    {
        assert forall |i: int|
            #![auto]
            0 <= i < a.len() ==> a[i] >= 0 by {
            // Local proof for arbitrary i goes here
        };

        // Example with explicit trigger that mentions bound var i:
        assert forall |i: int| 0 <= i < a.len() ==> #[trigger] a[i] >= 0 by {
        };

        // Example with two variables and multiple triggers:
        assert forall |i: int, j: int|
            0 <= i < a.len() && 0 <= j < a.len() ==> #[trigger] a[i] == a[j] ==> i == j by {
        };
    }
}
