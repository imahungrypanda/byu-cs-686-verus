# Story Review: Homework 2 Requirements Coverage

**Reviewers:** PM Agent + Architect Agent
**Date:** Review Session
**Subject:** Completeness check of hw2-stories.md against hw2-recursion-and-loops.md

---

## PM Review: Requirements Coverage Analysis

### Problem 1: Factorial - ✅ COMPLETE

**Homework Requirements:**

1. ✅ Write recursive specification → **AC #1**
2. ✅ Prove factorial(n) >= 1 → **AC #2**
3. ✅ Prove monotonic (i <= j ==> factorial(i) <= factorial(j)) → **AC #3**
   - ✅ Includes note about `lemma_mul_inequality` if not using `nonlinear_arith`
4. ✅ Write recursive implementation → **AC #4**
   - ✅ Includes requirement: returns same value when `factorial(n as nat) <= usize::MAX`
   - ✅ Includes requirement: uses monotonic lemma for overflow/underflow reasoning
5. ✅ Write iterative implementation → **AC #5**
   - ✅ Includes requirement: returns same value when `factorial(n as nat) <= usize::MAX`
   - ✅ Includes requirement: uses monotonic lemma
   - ✅ Includes requirement: invariant bounds iteration variable

**Hints Coverage:**

- ✅ Can write `#[test]` functions → **Dev Notes**
- ✅ Control flow in proofs → **Dev Notes**
- ✅ Use `assert` to figure out where Verus is stuck → **Dev Notes**
- ✅ Rewrite engine effectiveness → **Dev Notes**

**PM Assessment:** ✅ **COMPLETE** - All 5 requirements and hints covered.

---

### Problem 2: Sum to N - ✅ COMPLETE

**Homework Requirements:**

1. ✅ Repeat same pattern → **AC #1, #4**
2. ✅ Prove `n * (n + 1) / 2 == sum_to_n(n)` → **AC #3**
3. ✅ Need `lemma_sum_to_n_is_monotonic` → **AC #2**
   - ✅ Note: easy to write, trivial to prove, Verus doesn't need help
4. ✅ Need `lemma_mul_is_commutative` (if not using `nonlinear_arith`) → **AC #3**
5. ✅ Need `lemma_mul_is_distributive_add` → **AC #3**
   - ✅ Includes specific use case: `n * (n - 1) + n + n == n * ((n - 1) + 2)`
6. ✅ Recursive and iterative implementations → **AC #4**

**PM Assessment:** ✅ **COMPLETE** - All requirements covered, including specific lemma usage.

---

### Problem 3: GCD - ⚠️ MINOR GAP IDENTIFIED

**Homework Requirements:**

1. ✅ Repeat same pattern → **AC #1, #4**
2. ✅ Prove `lemma_gcd_positive` → **AC #2**
   - ✅ Requires: `!(a == 0 && b == 0)`
   - ✅ Ensures: `0 < gcd(a, b)`
3. ✅ Prove `lemma_gcd_divides` → **AC #3**
   - ✅ Requires: `!(a == 0 && b == 0)`
   - ✅ Ensures: `a % gcd(a, b) == 0` and `b % gcd(a, b) == 0`
   - ✅ All required lemmas listed:
     - ✅ `lemma_gcd_positive`
     - ✅ `lemma_fundamental_div_mod`
     - ✅ `lemma_mod_adds`
     - ✅ `lemma_mod_mul_zero`
4. ⚠️ **GAP:** `lemma_mod_mul_zero` implementation not explicitly called out as separate task
   - Currently mentioned in AC #3 and Dev Notes
   - Homework provides complete implementation code
   - Should be explicit task/subtask
5. ✅ Recursive and iterative implementations → **AC #4**
   - ✅ Note: implementations trivial to prove
   - ✅ Note: iterative invariant is tricky part

**PM Assessment:** ⚠️ **MOSTLY COMPLETE** - Missing explicit task for implementing `lemma_mod_mul_zero` (though it's mentioned).

---

### Problem 4: Integer Power - ⚠️ IMPLEMENTATIONS NOT EXPLICITLY REQUIRED

**Homework Requirements:**

1. ✅ Define `pow(n: nat, k: nat) -> nat` → **AC #1**
   - ✅ Recursion over exponent k
   - ✅ `decreases(k)`
   - ✅ Base case: `k == 0` returns 1
   - ✅ Recursive case: `n * pow(n, k - 1)`
2. ✅ Prove `pow(n, 0) == 1` → **AC #2**
3. ✅ Prove `pow(n, k+1) == n * pow(n, k)` → **AC #3**
4. ⚠️ **CLARIFICATION NEEDED:** Homework says "Prove typical properties" but doesn't explicitly require implementations
   - Story includes implementations in AC #4
   - This may be reasonable extension, but not explicitly required

**PM Assessment:** ⚠️ **COMPLETE FOR REQUIREMENTS** - Implementations are reasonable extension beyond stated requirements.

---

## Architect Review: Technical Completeness

### Story Structure Assessment

**✅ Strengths:**

1. Clear acceptance criteria with Given/When/Then format
2. Proper task breakdown with subtasks
3. Dev notes include relevant hints and patterns
4. References to source materials
5. Stories are appropriately sized for single dev sessions

**⚠️ Technical Concerns:**

1. **Story 3 - GCD:**

   - `lemma_mod_mul_zero` implementation should be explicit task
   - The homework provides the complete implementation, so this should be a clear subtask
   - Current: Mentioned in AC #3 and Dev Notes
   - Recommended: Add as explicit Task/Subtask

2. **Story 4 - Integer Power:**

   - Implementations not explicitly required by homework
   - However, following the pattern from other problems, this is reasonable
   - Consider noting this is an extension beyond requirements

3. **Missing Technical Details:**

   - No explicit mention of `nonlinear_arith` mode usage guidance
   - Homework notes most proofs can use `nonlinear_arith` except GCD
   - Could add to Dev Notes for clarity

4. **Loop Invariant Guidance:**
   - Story 3 notes "iterative invariant is tricky part" but doesn't provide guidance
   - Homework notes: "invariants that relate to the post-condition in the `ensures`"
   - Could strengthen Dev Notes with this guidance

---

## Recommendations

### Critical (Must Fix)

1. **Story 3 - Add explicit task for `lemma_mod_mul_zero`:**
   - Add as Task 3.5 or subtask under Task 3
   - Include the provided implementation from homework
   - Make it clear this is a prerequisite for `lemma_gcd_divides` proof

### Important (Should Fix)

2. **Story 3 - Strengthen loop invariant guidance:**

   - Add to Dev Notes: "Loop invariants must relate to the post-condition in the `ensures` clause"
   - Reference Section 5.3 from homework notes

3. **All Stories - Add `nonlinear_arith` mode guidance:**
   - Note in Dev Notes: "Most proofs can use `nonlinear_arith` mode except GCD proofs"
   - Reference Section 11.2 for GCD-specific guidance

### Nice to Have

4. **Story 4 - Note implementation extension:**
   - Add note that implementations are extension beyond stated requirements
   - But reasonable given pattern from other problems

---

## Final Verdict

**PM Verdict:** ✅ **APPROVED WITH MINOR REVISIONS**

- All core requirements covered
- One minor gap: explicit `lemma_mod_mul_zero` task
- Implementations for Story 4 are reasonable extension

**Architect Verdict:** ✅ **APPROVED WITH ENHANCEMENTS**

- Technical structure is sound
- Stories are well-scoped
- Minor enhancements to Dev Notes would improve clarity

**Overall:** Stories are **95% complete**. Recommended fixes are minor and can be addressed quickly.

---

## Action Items

1. [ ] Add explicit task/subtask for `lemma_mod_mul_zero` implementation in Story 3
2. [ ] Strengthen loop invariant guidance in Story 3 Dev Notes
3. [ ] Add `nonlinear_arith` mode usage guidance to Dev Notes across stories
4. [ ] (Optional) Note that Story 4 implementations are extension beyond requirements
