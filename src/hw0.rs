use vstd::prelude::*;

verus! {

// Homework 0 solutions go here
spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

// Example function to demonstrate structure
pub fn run_examples() {
    // Add your homework 0 examples here
    assert(min(10, 20) == 10);
    assert(min(-10, -20) == -20);
    assert(forall|i: int, j: int| min(i, j) <= i && min(i, j) <= j);
    assert(forall|i: int, j: int| min(i, j) == i || min(i, j) == j);
    assert(forall|i: int, j: int| min(i, j) == min(j, i));
}

} // verus!
