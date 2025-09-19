// Verus Recursive Exec Function Template
// Reference: https://verus-lang.github.io/verus/guide/recursion_loops.html#recursive-exec-and-proof-functions-proofs-by-induction

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Template for recursive exec functions with termination proofs
    pub exec fn recursive_exec_function(n: u64) -> (result: u64)
        requires
            n <= 100,  // Prevent stack overflow
        ensures
            result == recursive_spec_function(n as nat),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            let recursive_result = recursive_exec_function(n - 1);
            n + recursive_result
        }
    }

    // Helper spec function for verification
    spec fn recursive_spec_function(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + recursive_spec_function((n - 1) as nat)
        }
    }

    // Example: Factorial with verification
    pub exec fn factorial_exec(n: u64) -> (result: u64)
        requires
            n <= 20,  // Prevent overflow
        ensures
            result == factorial_spec(n as nat),
        decreases n,
    {
        if n == 0 {
            1
        } else {
            let recursive_result = factorial_exec(n - 1);
            n * recursive_result
        }
    }

    spec fn factorial_spec(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else {
            n * factorial_spec((n - 1) as nat)
        }
    }
}
