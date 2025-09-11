use vstd::prelude::*;

verus! {

fn octuple(x1: i8) -> i8 {
    let x2 = x1 + x1;
    let x4 = x2 + x2;
    x4 + x4
}


// Example function to demonstrate structure
pub fn run_examples() {
    // Add your homework 1 examples here
    // Use assert statements instead of println! for Verus
    assert(true); // Placeholder - replace with your actual homework 1 examples
}

} // verus!
