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
- Termination: <decreases clause / argument>
- Edge cases: <list>
- Open questions / follow-ups: <list>

Reference: https://verus-lang.github.io/verus/guide/overview.html
