use vstd::prelude::*;

verus! {

pub mod problem1 {
    use super::*;

    spec fn factorial_spec(n: nat) -> nat
        decreases
            n
    {
        if n == 0 {
            1
        } else {
            let m = (n - 1) as nat;
            factorial_spec(m) * n
        }
    }

    // Prove that factorial(n) >= 1
    proof fn factorial_proof(n: nat)
        by (nonlinear_arith)
        ensures
            factorial_spec(n) >= 1,
        decreases n,
    {
        if n == 0 {
            // Base case: factorial(0) = 1
        } else {
            // Inductive case: assume factorial(n-1) >= 1
            let m = (n - 1) as nat;
            factorial_proof(m);
        }
    }

    pub fn run_examples() {
        assert(factorial_spec(0) == 1);
        assert(factorial_spec(1) == 1);
        assert(factorial_spec(2) == 2);
        assert(factorial_spec(3) == 6);
        assert(factorial_spec(4) == 24);
        assert(factorial_spec(5) == 120);
        assert(factorial_spec(6) == 720);
        assert(factorial_spec(7) == 5040);
        assert(factorial_spec(8) == 40320);
        assert(factorial_spec(9) == 362880);
        assert(factorial_spec(10) == 3628800);
    }
}

pub mod problem2 {

    pub fn run_examples() {
        assert(true);
    }
}

pub mod problem3 {

    pub fn run_examples() {
        assert(true);
    }
}


} // verus!
