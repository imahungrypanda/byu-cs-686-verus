// Verus Loop Invariant Template
// Reference: https://verus-lang.github.io/verus/guide/overview.html

#![allow(unused_imports)]
use vstd::prelude::*;

verus! {
    pub exec fn sum_prefix(a: &Vec<u64>) -> (s: u64)
    {
        let mut i: usize = 0;
        let mut acc: u64 = 0;
        while i < a.len()
            invariant
                i <= a.len(),
        {
            acc = acc + a[i];
            i = i + 1;
        }
        acc
    }
}
