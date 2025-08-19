
# Homework 4

The goal if this homework is to understand how `verus` constructs proofs for recursion and looping structures using induction.

Please read, and review, the [weakest pre-conditions for loops](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/wp-for-loops.md) lecture notes.

## Problems

Write a paper-pencil proofs using weakest pre-condition calculus in each of the following questions.

Please follow these general guidelines for the paper-pencil proofs:

1. State an expression for the weakest precondition of the program.
1. State the goal of the proof: `P ==> wp(S,Q)`
1. Proceed to calculate the weakest precondition of the program by applying the appropriate inference rules.

Also, be mindful of the following

* If the rule application resulted in a new statement, simply continue with the proof in the same way.
* If it resulted in a logical formula, explain why the formula is valid.
* If it resulted in several new sub-goals or conjuncts, you may pick one of them and continue proving that one. When the first sub-goal has been proved true, don't forget that you have to go back and prove the other ones, too. Number the intermediate results if there is any danger of confusion.
* If you used the loop invariant rule, clearly state which formula you are using as invariant.

The proofs can be rather lengthy. You can copy and paste to avoid excessive typing. When you are dealing with large formulas in the pre- or post-condition you can introduce names to abbreviate them. Just keep in mind that when you are applying an update to a formula you have to unfold the abbreviation first before you apply the update (i.e., you need to substitute through the entire formula).

Whenever you are asked to implement something using `verus` you should:

1. Write a file with a *rs* extension corresponding to the program
1. Make sure `verus` can prove your program correct

### Problem 1

The following iterative implementation of multiplication proves out in `verus`. Complete a manual paper-pencil proof for it too (including termination). Do not use the lemma calls to prove out the `assert` statements; rather, use algebra, and algebraic axioms, since the lemma calls only serve to teach `verus` the same things.

```rust
pub exec fn q3(n0: usize, m0: usize) -> (res: usize)
    requires
        m0 != 0,
        n0 * m0 <= usize::MAX
    ensures
        n0 * m0 == res,
{
    let mut res: usize = 0;
    let mut n = n0;

    while 0 < n
        invariant
            m0 != 0,
            n0 * m0 <= usize::MAX,
            n0 * m0 == res + n * m0,
        decreases n,
    {
        assert(res + m0 <= n0 * m0) by {
            lemma_mul_left_inequality(m0 as int, 1, n as int);
        }
        res = res + m0;
        n = n - 1;
        assert(n0 * m0 == res + n * m0) by {
            lemma_mul_is_distributive_add(m0 as int, n as int, 1);
            lemma_mul_basics(m0 as int);
        };
    }
    res
}
```

### Problem 2

[hw2-recursion-loops](./hw2-recursion-and-loops.md) had you write the recursive `sum_to_n` implementation that is equivalent to it's specification which we know from the lemma is equivalent to `n * (n + 1) / 2`. Complete a manual, paper-pencil, proof of the same property. In other words, prove the following for your recursive implementation. Ignore anything related to overflow in the proof and use algebra for all the simplification.

```rust
exec fn sum_to_n_rec_impl(n: usize) -> (sum: usize)
    requires
        n * (n + 1) \ 2 <= usize::MAX,
    ensures
        n * (n + 1) \ 2 == sum,
    decreases n,
```

## Problem 3

Repeat the same proof as [Problem 2](#problem-2) only this time for the iterative version of `sum_to_n`. As before, ignore anything related to overflow and use algebra for all the simplification.
