# Verus Overview (Quick Reference)

Source: https://verus-lang.github.io/verus/guide/overview.html

## What is Verus?

Verus is a static verification toolchain for Rust that proves functional correctness using SMT solving (Z3). It augments Rust with specification and proof constructs while keeping checks at compile time (no runtime cost).

## Goals and Approach

- Functional correctness for systems code
- Three facets in one:
  - Spec language: pure math (`int`, `nat`, `forall`, `exists`, `==>`, `==`)
  - Proof language: structured proofs (`assert ... by { ... }`, proof functions, induction)
  - Exec language: Rust subset for real code
- Generates small verification conditions closely aligned with SMT logic

## Core Concepts

- Function specs: `requires` (preconditions), `ensures` (postconditions), `returns`
- Modes: spec / proof / exec; ghost and tracked variables
- Libraries: mathematical `Seq`, `Set`, `Map`; exec `Vec`
- Quantifiers and triggers: `forall`, `exists`, trigger annotations
- Termination: `decreases` clauses, fuel for recursion
- Visibility and performance: `reveal`, `hide`, `opaque`, module boundaries

## Workflow

1. Write exec Rust with specs (pre/postconditions, invariants)
2. Add proofs (proof blocks, lemmas), encode inductions/calculations
3. Iterate with SMT guidance (invariants, triggers, reveal/opaque)
4. Keep proofs modular and performant (profiling, splitting queries)

## Strengths and Limitations

- Strengths: integration with Rust ownership/borrowing; strong automation for many logical/arithmetic proofs; supports recursion, loops with invariants, traits, closures, arrays; disciplined `unsafe` patterns
- Limitations: nonlinear arithmetic and quantifiers often need guidance; `Seq`/`Set`/`Map` libraries are axiomatized (incomplete); termination and trigger tuning common

## Use Cases

- Verified data structures (e.g., BST case study)
- Proving absence of overflow
- Pointers/cells, concurrency patterns
- Encapsulating invariants via types/modules

## Getting Started

- CLI or VS Code usage
- Project setup with Rust crates and docs generation

## Advanced Patterns

### Specification Design

- **Helper specs**: Create small, focused specification functions (e.g., `elements_s_lt_x`, `elements_s_ge_x`)
- **`recommends` clauses**: Use for preconditions that should be checked but don't fail verification
- **Type conversion specs**: Create spec functions to convert between types (e.g., `seq_usize_to_int`)

### Recursive Specifications

- **`decreases` clauses**: Essential for recursive specs to ensure termination
- **Core vs wrapper specs**: Separate core recursive logic from boundary checks
- **Comprehensive postconditions**: Match all possible return cases in `ensures` clauses

### Loop Implementation

- **Loop invariants**: Maintain mathematical properties during iteration
- **Ghost variables**: Use `ghost` to track mathematical state without runtime cost
- **Invariant maintenance**: Assert properties at key points in the loop body

### Proof Strategy

- **Proof functions**: Create dedicated proof functions for complex properties
- **Test proofs**: Use proof functions to verify specifications work correctly
- **Assertion chaining**: Use `assert ... by { ... }` to chain proof steps

### Recursive Proof Patterns

- **Inductive proofs**: Use `decreases` clause to ensure termination
- **Base case handling**: Handle the termination condition explicitly
- **Recursive calls**: Use the proof function recursively with smaller arguments
- **Key insight**: Show that recursive arguments get smaller (e.g., `b % a < a`)
- **Example pattern**:
  ```rust
  proof fn lemma_property(x: nat)
      requires precondition,
      ensures postcondition,
      decreases x,
  {
      if x == 0 {
          // Base case: prove property directly
      } else {
          // Inductive case: show recursive call works
          assert(smaller_condition);
          lemma_property(smaller_x);
      }
  }
  ```

## vstd Library

The Verus standard library (`vstd`) provides essential utilities and datatypes for proofs and runtime functionality. Key modules include:

### Arithmetic Module (`vstd::arithmetic`)

- **`mul`**: Multiplication properties and lemmas
  - `lemma_mod_multiples_basic`: Proves multiples of a number are divisible by that number
  - `lemma_mul_is_commutative`: Commutativity of multiplication
  - `lemma_mul_is_distributive`: Distributivity of multiplication
- **`div_mod`**: Division and modulo properties
  - `lemma_fundamental_div_mod`: Fundamental division property
  - `lemma_mod_adds`: Modular arithmetic addition properties

### Other Key Modules

- **`seq`**: Mathematical sequences with specifications
- **`set`**: Mathematical sets with specifications
- **`map`**: Mathematical maps with specifications
- **`prelude`**: Common imports and utilities

### Usage Pattern

```rust
use vstd::arithmetic::mul::lemma_mod_multiples_basic;
use vstd::arithmetic::div_mod::lemma_fundamental_div_mod;
```

## Handy Keywords

`requires`, `ensures`, `returns`, `invariant`, `forall`, `exists`, `assert ... by`, `reveal`, `opaque`, `decreases`, `ghost`, `tracked`, `Seq`, `Set`, `Map`, `recommends`, `subrange`

## External Resources

- [vstd Documentation](https://verus-lang.github.io/verus/verusdoc/vstd/index.html)
