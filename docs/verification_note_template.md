# Verification Note Template

- Title: <module or function>
- Context: <what is being verified and why>
- Specs:
  - requires: <list>
  - ensures: <list>
  - invariants: <list>
- Proof strategy:
  - <high-level plan>
- SMT guidance:
  - triggers: <notes>
  - reveal/opaque: <notes>
  - by (nonlinear_arith): Use for multiplication/division inequalities (e.g., n \* x >= 1)
  - by (compute): Use for arithmetic that can be computed directly
  - by (bit_vector): Use for bitwise operations
- Recursive/Iterative Function Pattern:
  - Spec: `spec fn func_spec(n: nat) -> nat { if n == 0 { base } else { func_spec((n-1) as nat) op n } }`
  - Proofs: `proof fn func_proof(n: nat) by (nonlinear_arith) ensures func_spec(n) >= 0`
  - Monotonic: `proof fn func_monotonic(i: nat, j: nat) by (nonlinear_arith) ensures i <= j ==> func_spec(i) <= func_spec(j)`
  - Recursive: `exec fn func_rec_impl(n: usize) -> usize { if n == 0 { base } else { let r = func_rec_impl(n-1); n op r } }`
  - Iterative: Use loop invariant `result == func_spec(i as nat)` and overflow proof with monotonic lemma
  - Key tactics: `group_mul_properties`, `nonlinear_arith`, monotonic lemmas, preconditions in invariants
- Termination: <decreases clause / argument>
- Edge cases: <list>
- Open questions / follow-ups: <list>

Reference: https://verus-lang.github.io/verus/guide/overview.html
