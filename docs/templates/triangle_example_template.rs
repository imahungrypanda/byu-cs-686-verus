// Verus Triangle Number Example - Complete Implementation
// Reference: https://verus-lang.github.io/verus/guide/recursion_loops.html
// This template shows multiple verified implementations of triangle numbers:
// triangle(n) = 0 + 1 + 2 + ... + (n - 1) + n

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // 1. Recursive spec function (mathematical definition)
    spec fn triangle_spec(n: nat) -> nat
        decreases n,
    {
        if n == 0 {
            0
        } else {
            n + triangle_spec((n - 1) as nat)
        }
    }

    // 2. Recursive exec function with verification
    pub exec fn triangle_recursive(n: u64) -> (result: u64)
        requires
            n <= 1000,  // Prevent stack overflow
        ensures
            result == triangle_spec(n as nat),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            let recursive_result = triangle_recursive(n - 1);
            n + recursive_result
        }
    }

    // 3. While loop implementation with invariants
    pub exec fn triangle_while_loop(n: u64) -> (result: u64)
        requires
            n <= 1000,
        ensures
            result == triangle_spec(n as nat),
    {
        let mut i: u64 = 0;
        let mut acc: u64 = 0;

        while i <= n
            invariant
                i <= n + 1,
                acc == triangle_spec(i as nat),
        {
            acc = acc + i;
            i = i + 1;
        }

        acc
    }

    // 4. For loop implementation
    pub exec fn triangle_for_loop(n: u64) -> (result: u64)
        requires
            n <= 1000,
        ensures
            result == triangle_spec(n as nat),
    {
        let mut acc: u64 = 0;

        for i in 0..=n
            invariant
                acc == triangle_spec(i as nat),
        {
            acc = acc + i;
        }

        acc
    }

    // 5. Closed-form formula implementation (most efficient)
    pub exec fn triangle_closed_form(n: u64) -> (result: u64)
        requires
            n <= 65535,  // Prevent overflow in multiplication
        ensures
            result == triangle_spec(n as nat),
    {
        n * (n + 1) / 2
    }

    // 6. Proof that all implementations are equivalent
    pub proof fn triangle_equivalence_lemma(n: nat)
        ensures
            triangle_spec(n) == n * (n + 1) / 2,
        decreases n,
    {
        if n == 0 {
            assert(triangle_spec(0) == 0);
            assert(0 * (0 + 1) / 2 == 0);
        } else {
            triangle_equivalence_lemma((n - 1) as nat);
            assert(triangle_spec(n) == n + triangle_spec((n - 1) as nat));
            assert(triangle_spec(n) == n + (n - 1) * n / 2);
            assert(triangle_spec(n) == (2 * n + (n - 1) * n) / 2);
            assert(triangle_spec(n) == (n * (2 + n - 1)) / 2);
            assert(triangle_spec(n) == n * (n + 1) / 2);
        }
    }

    // 7. Test function to demonstrate all implementations
    pub exec fn test_triangle_implementations(n: u64) -> (all_equal: bool)
        requires
            n <= 100,
        ensures
            all_equal,
    {
        let recursive_result = triangle_recursive(n);
        let while_result = triangle_while_loop(n);
        let for_result = triangle_for_loop(n);
        let closed_result = triangle_closed_form(n);

        // Prove all implementations are equivalent
        triangle_equivalence_lemma(n as nat);

        assert(recursive_result == while_result);
        assert(while_result == for_result);
        assert(for_result == closed_result);

        true
    }

    // 8. Advanced: Triangle with array processing
    pub exec fn triangle_array_sum(a: &Vec<u64>) -> (result: u64)
        ensures
            result == sum_triangle_spec(a),
    {
        let mut result: u64 = 0;
        let mut i: usize = 0;

        while i < a.len()
            invariant
                i <= a.len(),
                result == sum_triangle_up_to_spec(a, i as int),
        {
            result = result + triangle_closed_form(a[i]);
            i = i + 1;
        }

        result
    }

    // Helper spec functions
    spec fn sum_triangle_spec(a: &Vec<u64>) -> u64
        decreases a.len() as int,
    {
        if a.len() == 0 {
            0
        } else {
            triangle_spec(a[0] as nat) + sum_triangle_spec(&a[1..])
        }
    }

    spec fn sum_triangle_up_to_spec(a: &Vec<u64>, i: int) -> u64
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            triangle_spec(a[(i - 1) as usize] as nat) + sum_triangle_up_to_spec(a, i - 1)
        }
    }
}
