# Homework 5

    Chapter [6. Datatypes: Structs and Enums](https://verus-lang.github.io/verus/guide/datatypes.html) and Chapter [7: Libraries](https://verus-lang.github.io/verus/guide/vstd.html). This homework has you write functional specifications, proofs, and implementations for computation involving basic collections.

# Problems

## Problem 1 - Count occurrences

Write a spec `count(s: Seq<int>, x: int) -> int` that returns how many times `x` appears in `s`. Implement `count_vec(v: Vec<isize>, x: isize) -> usize` iteratively and prove that it refines the spec.

## Problem 2 - Sum of a sequence

Write a spec `sum_spec(s: Seq<usize>) -> int` that returns the mathematical sum of the elements of `s`. Then implement `sum(s: Vec<usize>) -> usize` iteratively and prove that it refines the spec.

This problem is challenging because you have state that none of the individual additions performed while computing the sum overflow/underflow in the pre-condition for `sum(s: Vec<usize>) -> usize`:

$$\forall k, 0 \leq k \leq |s| \implies \mathtt{isize::MIN} <= \mathtt{sum}\_\mathtt{spec}(s\mathtt{@}.\mathtt{subrange}(0, k)) <= \mathit{isize::MAX}$$

Proving the iterative loop in the implementation has this property requires a lemma that states for $0 \leq i \le |s|$:

$$
\mathtt{sum\_spec}(s.\mathtt{subrange}(0, i + 1)) == \mathtt{sum\_spec}(s.\mathtt{subrange}(0, i)) + s[i]
$$

There are many ways to prove out the above lemma, depending on how `sum_spec` is written, but likely the following lemma will be needed for an sequence `s` and `usize` `x`:

$$
\mathtt{sum\_spec}(s + \mathtt{seq!}[x]) == \mathtt{sum\_spec}(s) + x
$$

That lemma will need to be inductive. The base case is when $|s| == 0$. The inductive step is the recursive call that drops the last element from `s` and makes that element `x`.

When using member methods of `Seq` it is sometimes necessary to _reveal_ those methods for the proofs especially if they are used within a specification. But it also depends on how the spec is written as to whether or not there are methods that need to be revealed explicitly with fuel.

## Problem 3 - Remove consecutive duplicates (run squashing)

Write a spec for `dedup_runs_spec(s: Seq<int>) -> Seq<int>` that removes adjacent duplicates (keeps the first of each run). Prove that the spec guarantees no consecutive duplicates preserves all other elements in the source array. So for `r = dedup_runs_spec(s)`

$$
\forall i (0 <= i < r.len() - 1 \implies r[i] \neq r[i + 1])
$$

And

$$
\forall i (0 <= i < r.len() \implies \exists j (i <= j < j.len() \wedge s[j] == r[i]))
$$

Implement `dedup_runs(v: &Vec<isize>) -> Vec<isize>` iteratively and prove refinement relative to the spec.

# Problem 4 - Merge sort

Write a spec for merge sort. Prove the final list is a sorted permutation of the original list. Implement merge sort and prove it refines the spec.

## Notes from reading

* Section 6.2, `enum` can use structure notation `{}` for attributes with names or tuple notation `()` for attributes that are just types. Tuple notation has to use the `tuple` syntax.
* Section 6.2, `matches` works with `|||` and `&&&` which is more readable then using implication.
* Section 7.1, `set`, `map`, and `seq` can be of arbitrary size and `set` and `map` can by infinite.
* Section 7.1, extensional equality, `=~=`, forces the SMT solver to check every element in a collection rather than just how the collections where constructed to determine equivalence. If `s1 =~= s2` then `s1 == s2`. `verus` automatically promotes `==` to `=~=` for collections in `assert`, `ensure`, and `invariant`.
* Section 7.2, a view maps an executable collection in the `std` to its mathematical counterpart is `vstd`. Support for `Vec` is solid. Looks like some limited support for `HashSet` and `HashMap`. But always use `view` (`@`) to move from implementation to a specification equivalent when writing specifications about the implementation. So all the specifications of a `v:Vec<int>` should be in terms of a `Seq<int>` using the view `v@`.
* You have to read the code for the `seq`, `set`, and `map`. There are a bunch of things you can do with `seq`.
