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

## Handy Keywords
`requires`, `ensures`, `returns`, `invariant`, `forall`, `exists`, `assert ... by`, `reveal`, `opaque`, `decreases`, `ghost`, `tracked`, `Seq`, `Set`, `Map`
