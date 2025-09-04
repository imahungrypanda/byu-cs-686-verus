// Verus Loop Invariant Template
// Reference: https://verus-lang.github.io/verus/guide/overview.html

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    pub exec fn sum_prefix(a: &Vec<u64>) -> (s: u64)
        requires
            // e.g., a.len() <= 1_000_000
        ensures
            // s is the sum of elements of a
    {
        let mut i: usize = 0;
        let mut acc: u64 = 0;
        while i < a.len()
            invariant
                // 0 <= i <= a.len()
                // acc equals sum of a[0..i)
        {
            acc = acc + a[i];
            i = i + 1;
        }
        acc
    }
}
