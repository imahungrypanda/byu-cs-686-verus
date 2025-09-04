#![allow(unused_imports)]

use vstd::prelude::*;

verus! {
    pub exec fn inc_bad(x: u64) -> (y: u64)
        requires x < u64::MAX
        ensures y == x + 2
    {
        x + 1
    }
}

fn main() {
    println!("Hello, Verus!");
}
