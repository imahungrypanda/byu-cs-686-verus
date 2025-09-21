// Import all homework modules
mod hw0;
mod hw1_basic_specifications;
mod hw2_recursion_and_loops;
mod hw3;
mod hw4;

mod example_1;
// mod class;
use vstd::prelude::*;

verus! {

fn class_run_examples() {
    // class::mult::run_examples();
    // class::binary_search_class::run_examples();
}

fn main() {

    hw0::run_examples();

    // Run homework 1 examples
    hw1_basic_specifications::problem1::run_examples();
    hw1_basic_specifications::problem2::run_examples();
    hw1_basic_specifications::problem3::run_examples();

    // Run homework 2 examples (when implemented)
    hw2_recursion_and_loops::problem1::run_examples();
    hw2_recursion_and_loops::problem1::test_factorial_implementation();
    hw2_recursion_and_loops::problem2::run_examples();
    hw2_recursion_and_loops::problem3::run_examples();

    // Run homework 3 examples (when implemented)
    // hw3::run_examples();

    // Run homework 4 examples (when implemented)
    // hw4::run_examples();

    // Run reading 1 examples
    example_1::run_examples();

    class_run_examples();
}

} // verus!
