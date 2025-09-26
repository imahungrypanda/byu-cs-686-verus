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
    use super::*;

    // Sum to n spec
    spec fn sum_to_n_spec(n: nat) -> nat
        decreases
            n
    {
        if n == 0 {
            0
        } else {
            let m = (n - 1) as nat;
            sum_to_n_spec(m) + n
        }
    }

    // Prove that sum_to_n(n) >= 0
    proof fn sum_to_n_proof(n: nat)
        by (nonlinear_arith)
        ensures
            sum_to_n_spec(n) >= 0,
        decreases n,
    {
        if n == 0 {
        } else {
            let m = (n - 1) as nat;
            sum_to_n_proof(m);
        }
    }

    // Prove that sum_to_n is monotonic: i <= j ==> sum_to_n(i) <= sum_to_n(j)
    proof fn sum_to_n_monotonic(i: nat, j: nat)
        by (nonlinear_arith)
        ensures
            i <= j ==> sum_to_n_spec(i) <= sum_to_n_spec(j),
        decreases j,
    {
        if j == 0 {
        } else {
            sum_to_n_monotonic(i, (j - 1) as nat);
        }
    }

    // Recursive implementation of sum_to_n
    exec fn sum_to_n_rec_impl(n: usize) -> (result: usize)
        requires
            0 <= n <= usize::MAX,
            sum_to_n_spec(n as nat) <= usize::MAX,
        ensures
            result == sum_to_n_spec(n as nat),
        decreases n,
    {
        if n == 0 {
            0
        } else {
            let recursive_result = sum_to_n_rec_impl(n - 1);
            n + recursive_result
        }
    }

    // Iterative implementation of sum_to_n
    exec fn sum_to_n_iter_impl(n: usize) -> (result: usize)
        requires
            0 <= n <= usize::MAX,
            sum_to_n_spec(n as nat) <= usize::MAX,
        ensures
            result == sum_to_n_spec(n as nat),
    {
        let mut result: usize = 0;
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                result == sum_to_n_spec(i as nat),
                sum_to_n_spec(n as nat) <= usize::MAX,
            decreases n - i,
        {
            assert(result + (i + 1) <= usize::MAX) by {
                assert(result == sum_to_n_spec(i as nat));
                assert(sum_to_n_spec(i as nat) + (i + 1) == sum_to_n_spec((i + 1) as nat));
                sum_to_n_monotonic((i + 1) as nat, n as nat);
            }
            i = i + 1;
            result = result + i;
        }

        result
    }

    #[test]
    fn test_sum_to_n_implementation() {
        assert_eq!(sum_to_n_rec_impl(0), 0);
        assert_eq!(sum_to_n_rec_impl(1), 1);
        assert_eq!(sum_to_n_rec_impl(2), 3);
        assert_eq!(sum_to_n_rec_impl(3), 6);
        assert_eq!(sum_to_n_rec_impl(4), 10);
        assert_eq!(sum_to_n_rec_impl(5), 15);
    }

    pub fn run_examples() {
        assert(sum_to_n_spec(0) == 0);
        assert(sum_to_n_spec(1) == 1);
        assert(sum_to_n_spec(2) == 3);
        assert(sum_to_n_spec(3) == 6);
        assert(sum_to_n_spec(4) == 10);
        assert(sum_to_n_spec(5) == 15);
    }
}

pub mod problem3 {
    use super::*;

    spec fn gcd(a: nat, b: nat) -> nat
        decreases
            a
    {
        if a == 0 {
            b
        } else {
            gcd(b % a, a)
        }
    }

    proof fn lemma_gcd_positive(a: nat, b: nat)
        requires
            !(a == 0 && b == 0),
        ensures
            0 < gcd(a, b),
        decreases
            a,
    {
        if a == 0 {
            assert(b > 0);
        } else {
            assert(b % a < a);
            lemma_gcd_positive(b % a, a);
        }
    }

    // proof fn lemma_gcd_divides(a: nat, b: nat)
    //     requires
    //         !(a == 0 && b == 0),
    //     ensures
    //         a % gcd(a, b) == 0,
    //         b % gcd(a, b) == 0,
    // {}

    proof fn lemma_mod_mul_zero(x: int, q: int, m: int)
    requires
        m > 0,
        x % m == 0,
    ensures
        (x * q) % m == 0,
    {
        assume(true);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, m);
        vstd::arithmetic::mul::lemma_mul_is_associative(m, (x / m), q);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic((x / m) * q, m);
    }

    pub fn run_examples() {
        // Basic cases
        assert(gcd(0, 0) == 0);
        assert(gcd(0, 1) == 1);
        assert(gcd(1, 0) == 1);
        assert(gcd(1, 1) == 1);
        assert(gcd(1, 2) == 1);
        assert(gcd(2, 1) == 1);

        // Bigger examples - demonstrate the algorithm with larger numbers
        assert(gcd(48, 18) == 6) by {
            reveal_with_fuel(gcd, 10);
        };
        // assert(gcd(100, 20) == 20);
        // assert(gcd(252, 105) == 21);
        // assert(gcd(1071, 462) == 21);
        // assert(gcd(123456, 7890) == 6);
        // assert(gcd(987654321, 123456789) == 9);

        // // Edge cases with larger numbers
        // assert(gcd(1000000, 1) == 1);
        // assert(gcd(1, 1000000) == 1);
        // assert(gcd(1000000, 1000000) == 1000000);
        // assert(gcd(0, 1000000) == 1000000);
        // assert(gcd(1000000, 0) == 1000000);

        // // Prime numbers (should be 1)
        // assert(gcd(17, 19) == 1);
        // assert(gcd(97, 101) == 1);
        // assert(gcd(1009, 1013) == 1);

        // // Powers of 2
        // assert(gcd(64, 32) == 32);
        // assert(gcd(128, 64) == 64);
        // assert(gcd(1024, 512) == 512);

        // // Fibonacci numbers (consecutive Fibonacci numbers are coprime)
        // assert(gcd(21, 34) == 1);  // F(8) and F(9)
        // assert(gcd(34, 55) == 1);  // F(9) and F(10)
        // assert(gcd(55, 89) == 1);  // F(10) and F(11)

    }
}


} // verus!
