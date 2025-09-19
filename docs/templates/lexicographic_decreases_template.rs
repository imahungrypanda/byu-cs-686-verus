// Verus Lexicographic Decreases Template
// Reference: https://verus-lang.github.io/verus/guide/recursion_loops.html#lexicographic-decreases-clauses-and-mutual-recursion

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    // Template for lexicographic decreases with multiple arguments
    pub exec fn lexicographic_example(a: u64, b: u64) -> (result: u64)
        requires
            a <= 100 && b <= 100,
        ensures
            result == lexicographic_spec(a, b),
        decreases (a, b),  // Lexicographic ordering: (a,b) decreases
    {
        if a == 0 {
            b
        } else if b == 0 {
            a
        } else {
            lexicographic_example(a - 1, b - 1)
        }
    }

    spec fn lexicographic_spec(a: u64, b: u64) -> u64
        decreases (a, b),
    {
        if a == 0 {
            b
        } else if b == 0 {
            a
        } else {
            lexicographic_spec(a - 1, b - 1)
        }
    }

    // Template for mutual recursion
    pub exec fn even(n: u64) -> (result: bool)
        requires
            n <= 1000,
        ensures
            result == even_spec(n),
        decreases n,
    {
        if n == 0 {
            true
        } else {
            odd(n - 1)
        }
    }

    pub exec fn odd(n: u64) -> (result: bool)
        requires
            n <= 1000,
        ensures
            result == odd_spec(n),
        decreases n,
    {
        if n == 0 {
            false
        } else {
            even(n - 1)
        }
    }

    // Spec versions for verification
    spec fn even_spec(n: u64) -> bool
        decreases n,
    {
        if n == 0 {
            true
        } else {
            odd_spec(n - 1)
        }
    }

    spec fn odd_spec(n: u64) -> bool
        decreases n,
    {
        if n == 0 {
            false
        } else {
            even_spec(n - 1)
        }
    }

    // Template for complex lexicographic decreases
    pub exec fn complex_lexicographic(a: u64, b: u64, c: u64) -> (result: u64)
        requires
            a <= 50 && b <= 50 && c <= 50,
        ensures
            result == complex_lexicographic_spec(a, b, c),
        decreases (a, b, c),  // Triple lexicographic ordering
    {
        if a == 0 && b == 0 && c == 0 {
            0
        } else if a > 0 {
            complex_lexicographic(a - 1, b, c)
        } else if b > 0 {
            complex_lexicographic(a, b - 1, c)
        } else {
            complex_lexicographic(a, b, c - 1)
        }
    }

    spec fn complex_lexicographic_spec(a: u64, b: u64, c: u64) -> u64
        decreases (a, b, c),
    {
        if a == 0 && b == 0 && c == 0 {
            0
        } else if a > 0 {
            complex_lexicographic_spec(a - 1, b, c)
        } else if b > 0 {
            complex_lexicographic_spec(a, b - 1, c)
        } else {
            complex_lexicographic_spec(a, b, c - 1)
        }
    }

    // Template for decreases with condition - Verus doesn't support "when" in decreases
    // Instead, we use conditional logic in the function body
    pub exec fn conditional_decreases(n: u64, flag: bool) -> (result: u64)
        requires
            n <= 100,
        ensures
            result == conditional_decreases_spec(n, flag),
        decreases if flag { n } else { 0 },  // Conditional decreases clause
    {
        if !flag {
            0
        } else if n == 0 {
            0
        } else {
            conditional_decreases(n - 1, flag)
        }
    }

    spec fn conditional_decreases_spec(n: u64, flag: bool) -> u64
        decreases if flag { n } else { 0 },
    {
        if !flag {
            0
        } else if n == 0 {
            0
        } else {
            conditional_decreases_spec(n - 1, flag)
        }
    }
}
