# Homework 1

This homework covers [3. Basic specifications](https://verus-lang.github.io/verus/guide/specs.html) and [4. Specification code, proof code, executable code](https://verus-lang.github.io/verus/guide/modes.html). The intent is to learn to

1. Write specifications using `spec`.
1. Write specifications for executable functions using `requires` and `ensures`.
1. Create non-verified functions for output etc.
1. Use `assert`.
1. Write a specification, prove properties of the specification, and prove an implementation meets its specification.

# Problems

1. Given a `value: i32` and an range `[min: i32, max: i32]` with a positive `step: u16`, return `true` if and only if `value` is equal to one of the values that would be encountered stepping by `step` and starting at `min` and not exceeding `max`. Otherwise return `false`.

    * Write the specification for `spec fn spec_is_in_range_by_step(value: int, min: int, max: int, step: nat) -> (result: bool)`
    * Implement `exec fn is_in_range_by_step(value: i32, min: i32, max: i32, step: u16) -> (result: bool)`
    * Write a specification for `exec fn is_in_range_by_step(value: i32, min: i32, max: i32, step: u16) -> (result: bool)` that says result always matches `spec fn spec_is_in_range_by_step(value: int, min: int, max: int, step: nat) -> (result: bool)` and show that that is the case in a separate _"test"_ function that uses `assert` to prove out interesting corner cases. The _"test"_ function should be in the `verus!` block and not annotated with `#[test]` as by _"test"_ we mean, "see if `verus` is able to prove these assertions."

1. Given two `i32` values, return the absolute distance between the two values as a `u32` value.

    * Write the specification for `spec fn spec_absolute_difference(x:int, y:int) -> (result: nat)`
    * Prove that  `spec_absolute_difference(x:int, y:int)` is commutative: `spec_absolute_difference(x, y) == spec_absolute_difference(y, x)`
    * Implement `exec fn absolute_difference(x:i32, y:i32) -> (result: u32)`
    * Write a specification for `absolute_difference` that says that `result` always matches `spec_absolute_difference` and show that that is the case in a separate _"test"_ function that uses `assert` to prove out interesting corner cases.

1. Given a function that computes the median of three values, write a median-of-medians filter that uses the three-value median to approximate the median of five values. Write a proof that requires the input to be sorted and ensures that the median-of-medians filter is an approximation of the true median (i.e., given `a <= b <= c <= d <= e` the median-of-medians filter does not return `c`).

## Notes from Reading

* Section 3.1, `#[verifier::external_body]` indicates that there is a contract but the body itself is not verified. It enables the use of `println!` and other code that is not intended to be verified.
* Section 3.1, `&&&` and `|||` or the low precedence versions of `&&` and `||`. Useful for bulleted lists of conjunctions (disjunctions) expressions as it avoids needing parenthesis for precedence.
* Section 3.3, `usize::BITS`, `usize::MAX`, `isize::MIN`, and `isize::MAX` are ways to reason about machine dependent integer ranges --- `let x: isize = 0` would be an `int` in normal languages so its size depends on the machine architecture.
* Section 3.3, you can embed `let` expressions to improve readability and code flow as in the below. Not the use of the suffix on the constant to indicate type.

```
assert({
    let expected:isize = 80i8;
    expected == answer
});
```

* Section 3.3, integer arithmetic is ghost code is with `int` and `nat` regardless of the declared size. Use this feature to write about overflow in the specification (e.g., `requires x + y < 256` if `x` and `y` are type `u8`).
* Section 3.3, named arithmetic functions like `add(x, y)` do not widen to `int` or `nat`. Verus also understands `wrapped_add` and `checked_add` that can be in executable or ghost code.
* Section 3.4, `==` is always assumed to be an equivalence relation which is different than what Rust believes since the trait for a user defined type may not be implemented as an equivalence relation. So does that mean that Verus doesn't use the trait implementation? Not clear. Rust calls the `eq` function. Verus has a definition for what `==` means for structs and enums.
* Section 4, `exec` is the default function type of `exec`, `spec`, and `proof` so when the type is omitted it's `exec`.
* Section 4.1, the body of a `spec` function can be hidden with `closed` -- must specify `open` or `closed` in a module along with `pub` or not for a `spec`. A `proof` function can be used to provide a contract for the `spec` function if the function body is `closed` or too complex and usefully abstracted in a declarative contract. Requires a `proof {...}` to call the action `proof` function as in the below.

```
proof {
        lemma_min(10,20); // Brings the pre/post conditions for `min` into scope for the following assertion.
    }
    assert(min(10, 20) <= 10);
```

* Section 4.2, `assert(...) by {}` limits the scope of the proof block to just the assertion and then admits the assertion into the general scope.
* Section 4.3, Verus does not assume `proof` function are deterministic in the absence of a specification. A proof without post conditions has an arbitrary outcome regardless of the arguments.
* Section 4.3, `spec(checked)` will emit warnings in the `recommends` clause is violated.
* Section 4.4, ghost code can copy values of any type even in the absence of the `Copy` trait, and it can instantiate values of any type even in the absence of a constructor.
* Section 4.5, a `const` is like a `spec` function with no arguments. It can have an `exec` version with a post-condition. If the mode is omitted, `spec` or `exec`, then the `const` is dual mode.
* Section 4.5, `[verifier::when_used_as_spec(SPEC_DEF)]` enables specifying a `spec` function for an `exec` const.
* Section 4.5, `[verifier::non_linear]` seems useful for const declarations and _non-linear_ arithmetic.
