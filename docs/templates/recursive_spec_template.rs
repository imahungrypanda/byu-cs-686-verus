// Verus Recursive Spec Function Template
// Reference: https://verus-lang.github.io/verus/guide/recursion_loops.html#recursive-spec-functions-decreases-fuel

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Template for recursive spec functions with decreases clauses
    spec fn recursive_function(n: nat) -> nat
        decreases n,  // Termination condition - n decreases each recursive call
    {
        if n == 0 {
            // Base case
            0
        } else {
            // Recursive case - ensure argument decreases
            n + recursive_function((n - 1) as nat)
        }
    }

    // Example: Factorial function
    spec fn factorial(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            1
        } else {
            n * factorial((n - 1) as nat)
        }
    }

    // Example: Fibonacci (with lexicographic decreases for multiple arguments)
    spec fn fibonacci(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else if n == 1 {
            1
        } else {
            fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
        }
    }
}
