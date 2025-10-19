# Homework 3

The goal of this homework is to gain an understanding of [Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic) and the [weakest pre-condition calculus](https://en.wikipedia.org/wiki/Predicate_transformer_semantics) as a predicate transformer. These are the underlying foundation for `verus` and how it proves out programs.

Please read, and review, the [weakest pre-conditions](https://bitbucket.org/byucs329/byu-cs-329-lecture-notes/src/master/weakest-preconditions.md) lecture notes.

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

The function `m` does not implement the post-condition as reported by `verus`. Complete the proof by hand using weakest precondition calculus to figure out how to strengthen the `requires` clause in the specification. Confirm that `verus` is able to prove it out with the strengthened `requires`.

```rust
fn m(x: isize, y: isize) -> (result: (isize, isize))
    ensures
        result.0 > result.1
{
    if x > y {
        (x, y)
    } else {
        (y, x)
    }
}
```

### Problem 2

Complete the proof of the implementation by hand using weakest pre-condition calculus.

```rust
exec fn m(x0: isize) -> (x: isize)
    requires
        usize::MIN <= x0 - 3 <= usize::MAX
    ensures
        (x0 < 3 ==> x == 1),
        (x0 >= 3 ==> x < x0),
{
    let mut x = x0 - 3;
    if x < 0 {
        x = 1;
    } else {
        if true {
            x = x + 1;
        } else {
            x = 10;
        }
    }
    x
}
```

### Problem 3

Complete the proof of the implementation by hand using weakest pre-condition calculus.

```rust
spec fn is_median_spec(a: int, b: int, c: int, m: int) -> (bool) {
    ||| (m == a && (b <= a <= c || c <= a <= b))
    ||| (m == b && (a <= b <= c || c <= b <= a))
    ||| (m == c && (a <= c <= b || b <= c <= a))
}

spec fn median_spec(a: int, b: int, c: int) -> (int) {
    if (a >= b && a <= c) || (a >= c && a <= b) {
        a
    } else if (b >= a && b <= c) || (b >= c && b <= a) {
        b
    } else {
        c
    }
}
```
