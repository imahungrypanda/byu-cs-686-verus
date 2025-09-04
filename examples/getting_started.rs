#![allow(unused_imports)]

use vstd::prelude::*;

verus! {
    pub exec fn inc(x: u64) -> (y: u64)
        requires x < u64::MAX
        ensures y == x + 1
    {
        x + 1
    }
}

fn main() {
    println!("Hello, Verus!");
}
