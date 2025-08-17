# Homework 2

Chapter [4. Recursion and loops](https://verus-lang.github.io/verus/guide/recursion_loops.html). This homework has you follow the pattern for the `triangle` example from the reading several times. Doing it for the first time on your own is actually really hard. Then applying it again is easier. The biggest challenge is figuring out what `verus` needs to do the algebra. That knowledge comes from the [lemmas about arithmetic](https://verus-lang.github.io/verus/verusdoc/vstd/arithmetic/mul/index.html) in the [vstd library](https://verus-lang.github.io/verus/verusdoc/vstd/index.html). I've identified the set of lemmas I used in the solution for each problem. Figuring out where, when, and how to use them is still challenging. Be patient, and when needed, use AI to help.

# Problems

## Problem 1: factorial

Write a complete specification and implementation for `factorial` following the pattern for `triangle` in chapter [4. Recursion and Loops](https://verus-lang.github.io/verus/guide/recursion_loops.html).

1. Write a recursive specification for `factorial`.
1. Prove that `factorial(n) >= 1`
1. Prove that `factorial` is monotonic meaning that `i <= j ==> factorial(i) <= factorial(j)`. For this proof, you will need to use `vstd::arithmetic::mul::lemma_mul_inequality` after the recursive call in the proof.
1. Write a recursive implementation of `factorial` that always returns the same value as `factorial` when `factorial(n as nat) <= usize::MAX`. You will need the monotonic lemma from the previous step just as was required for `triangle` in order for Verus to reason about overflow and underflow.
1. Write an iterative implementation of `factorial` that always returns the same value as `factorial` when `factorial(n as nat) <= usize::MAX`. You will need the monotonic lemma again and the invariant needs to bound variable used for iteration.

Hints:
* You can write normal `#[test]` functions and use `cargo test` to be sure that your implementations work before attempting proofs.
* Control flow in proofs should follow the control flow of the specification. Use `assume(false)` to develop the proof path by path.
* The rewrite engine in `verus` is really good once it has the necessary lemmas. I've listed here all the lemmas that are needed for this problem and where they should appear.
* Use `assert` to figure out what `verus` is stuck and then apply lemmas to unstick it.


## Problem 2: sum of n

Repeat the same pattern as before only this time for the sum of `n` natural numbers, `sum_to_n`, and prove that `n * (n + 1) / 2 == sum_to_n(n)`. Things that you will need along the way:

* `lemma_sum_to_n_is_monotonic` (easy to write and trivial to prove -- `verus` doesn't need any help)
* `vstd::arithmetic::mul::lemma_mul_is_commutative` for the proof that `sum_to_n(n)` is equal to `n * (n + 1) / 2`
* `vstd::arithmetic::mul::lemma_mul_is_distributive_add` for the proof that `sum_to_n(n)` is equal to `n * (n + 1) / 2`. I used it to prove `assert(n * (n - 1) + n + n == n * ((n - 1) + 2))`.


## Problem 3: greatest common divisor (gcd)

Repeat the same pattern `gcd(a: nat, b: nat)` and prove the following lemmas:

```
proof fn lemma_gcd_positive(a: nat, b: nat)
    requires
        !(a == 0 && b == 0),
    ensures
        0 < gcd(a, b),

proof fn lemma_gcd_divides(a: nat, b: nat)
    requires
        !(a == 0 && b == 0),
    ensures
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
```

The proof for `lemma_gcd_divides` will need the following:

* `lemma_gcd_positive`
* `vstd::arithmetic::div_mod::lemma_fundamental_div_mod`
* `vstd::arithmetic::div_mod::lemma_mod_adds`
* `lemma_mod_mul_zero` given below.


```
proof fn lemma_mod_mul_zero(x: int, q: int, m: int)
    requires
        m > 0,
        x % m == 0,
    ensures
        (x * q) % m == 0,
{
    lemma_fundamental_div_mod(x, m);
    lemma_mul_is_associative(m, (x / m), q);
    lemma_mod_multiples_basic((x / m) * q, m);
}
```

The recursive and iterative implementations are trivial to prove with the only tricky part being the invariant for the iterative version.

# Notes from Reading

* Section 5.1, requiring termination needs more discussion as the issue stems from assumptions made by Hoare logic and what partial and total correctness mean.
* Section 5.1, `spec` functions are _functions_ in the full mathematical sense so they must be defined over the entire domain. The `recommends` clause is not enforced and it is not considered during verification. What this means is that the `decreases` clause can be complicated because it doesn't hold for parts of the domain that would normally be disallowed by the `recommends`. There are ways to state `decreases` to account for such issues.
* Section 5.2, `old` refers to the value in the _pre-state_ of the function. Unlike Dafny, both `requires` and `ensures` refer to the post-state of values (Dafny refers to pre-state in `requires` and post-state in `ensures`).
* Section 5.3, write invariants that relate to the post-condition in the `ensures` otherwise they are useless as the `invariant` is all that `verus` knows about what the loop does when proving the post-condition.
* Section 5.3, _weaker_ means more things make the predicate true so `p(x) = true` means that every `x` makes `p(x)` true; whereas _stronger_ means that fewer things make the predicate true so `p(x) = false` means no `x` makes `p(x)` true.
* Section 5.3, loop invariants **do not** inherit the pre-conditions; these must be state explicitly in the invariant. See `#[verifier::loop_isolation(false)]` to change this behavior.
* Section 5.3.1, add `ensures` for loops with `break` statements and scope out the invariant with `invariant_except_break`.

# Other problems


## Integer Power (n^k)

Define exponentiation by recursion over exponent k:
```
spec fn pow(n: nat, k: nat) -> nat
    decreases(k)
{
    if k == 0 {
        1
    } else {
        n * pow(n, k - 1)
    }
}
```
Termination: decreases on k.
Prove typical properties like pow(n, 0) == 1, or pow(n, k+1) == n * pow(n, k).
