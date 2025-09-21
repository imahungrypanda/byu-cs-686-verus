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
        } else {
            let m = (n - 1) as nat;
            factorial_proof(m);
        }
    }

    // Prove that factorial is monotonic: i <= j ==> factorial(i) <= factorial(j)
    proof fn factorial_monotonic(i: nat, j: nat)
        by (nonlinear_arith)
        ensures
            i <= j ==> factorial_spec(i) <= factorial_spec(j),
        decreases j,
    {
        if j == 0 {
            // Base case: j == 0, so i must also be 0
        } else {
            // Inductive case: assume the property holds for j-1
            factorial_monotonic(i, (j - 1) as nat);
        }
    }

    exec fn factorial_rec_impl(n: usize) -> (result: usize)
        requires
            0 <= n <= usize::MAX,
            factorial_spec(n as nat) <= usize::MAX,
        ensures
            result == factorial_spec(n as nat),
        decreases n,
    {
        if n == 0 {
            1
        } else {
            assert(factorial_spec((n - 1) as nat) <= usize::MAX) by {
                factorial_monotonic((n - 1) as nat, n as nat);
            }

            let recursive_result = factorial_rec_impl(n - 1);

            assert(recursive_result == factorial_spec((n - 1) as nat));
            assert(n * recursive_result <= usize::MAX) by {
                broadcast use vstd::arithmetic::mul::group_mul_is_commutative_and_distributive;
            }
            let result: usize = n * recursive_result;

            assert(recursive_result == factorial_spec((n - 1) as nat));
            assert(n * recursive_result == n * factorial_spec((n - 1) as nat));
            assert(factorial_spec((n - 1) as nat) * n == factorial_spec(n as nat));
            assert(n * recursive_result == factorial_spec((n - 1) as nat) * n) by {
                broadcast use vstd::arithmetic::mul::group_mul_is_commutative_and_distributive;
            };
            assert(result == factorial_spec(n as nat));

            result
        }
    }

    exec fn factorial_iter_impl(n: usize) -> (result: usize)
        requires
            0 <= n <= usize::MAX,
            factorial_spec(n as nat) <= usize::MAX,
        ensures
            result == factorial_spec(n as nat),
    {
        let mut result: usize = 1;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                result == factorial_spec(i as nat),
                factorial_spec(n as nat) <= usize::MAX,
            decreases n - i,
        {
            assert(result * (i + 1) <= usize::MAX) by {
                factorial_monotonic((i + 1) as nat, n as nat);
            }

            i = i + 1;
            result = result * i;
        }

        result
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

    pub exec fn test_factorial_implementation() {
        let result0 = factorial_rec_impl(0);
        let result1 = factorial_rec_impl(1);
        let result2 = factorial_rec_impl(2);
        let result3 = factorial_rec_impl(3);
        let result4 = factorial_rec_impl(4);
        let result5 = factorial_rec_impl(5);

        assert(result0 == 1);
        assert(result1 == 1);
        assert(result2 == 2);
        assert(result3 == 6);
        assert(result4 == 24);
        assert(result5 == 120);
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
