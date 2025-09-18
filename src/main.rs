// Import all homework modules
mod hw0;
mod hw1_basic_specifications;
mod hw2;
mod hw3;
mod hw4;

mod example_1;
mod class;
use vstd::prelude::*;

verus! {



fn main() {

    hw0::run_examples();

    // Run homework 1 examples
    hw1_basic_specifications::problem1::run_examples();
    hw1_basic_specifications::problem2::run_examples();

    // Run homework 2 examples (when implemented)
    // hw2::run_examples();

    // Run homework 3 examples (when implemented)
    // hw3::run_examples();

    // Run homework 4 examples (when implemented)
    // hw4::run_examples();

    // Run reading 1 examples
    example_1::run_examples();
    class::mult::run_examples();

    class::binary_search_class::run_examples();
}

} // verus!
