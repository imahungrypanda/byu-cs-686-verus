# Dijkstra Verification Plan

## Phase 1 – Fill the Spec Gap

- Prompts to run:
  - “Add lemmas that extend witness paths when relaxing edges (using `append_vertex_*` and `get_updated_distance`).”
  - “Prove that any concrete path yields an upper bound `sp_dist ≤ path_cost`.”

## Phase 2 – Relaxation Invariant

- Prompts to run:
  - “Use the new path witnesses to replace the `assume(...)` calls in `update_edges_preserves_state_inv`.”
  - “Show relaxed neighbors retain the upper-bound invariant and visited nodes stay exact.”

## Phase 3 – Visiting the Next Node

- Prompts to run:
  - “Prove that the node returned by `find_min_unvisited_spec` has distance equal to `sp_dist` once marked visited.”
  - “Strengthen `dijkstra_core_spec` to require/ensure `dijkstra_state_inv` before and after recursion.”

## Phase 4 – Top-Level Spec

- Prompts to run:
  - “Use the strengthened core lemma to establish that `dijkstra_spec` returns `sp_dist` (or `None`).”
  - “Run the Verus checker on `src/hw6_dijkstra.rs`.”

## Phase 5 – Executable Refinement

- Prompts to run:
  - “Annotate `dijkstra_exec` inside `verus!` with specs matching the loop invariant.”
  - “Prove the executable `dijkstra_exec` refines the specification.”
  - “Add lemmas that extend witness paths when relaxing edges (using `append_vertex_*` and `get_updated_distance`).”
  - “Prove that any concrete path yields an upper bound `sp_dist ≤ path_cost`.”






## Plan To Clear The Last Four Failures

- **`sp_dist_upper_bound_for_path` (rlimit)**
  - Split the proof: first get path length > 1, then handle recursive tail via a helper lemma so the SMT solver sees fewer quantifiers in one go.
  - Hint: prove a separate lemma that for any `path`, either it’s just the start node or you can show `is_path` for the tail and use it to bound the minimum.

- **`unvisited_core_lemma` recommendations + postcondition**
  - Before entering the `Option::Some(result_node)` branch, establish the bounds/visited facts so `is_cand`’s recommends (`0 ≤ i < dist.len()`) are met; e.g., bind `result_node` and `best` to local variables with explicit bounds, then reuse them in the forall/exist clauses.
  - Make sure recursive call decreases with a proof (e.g., show `start_node + 1 ≤ dist.len()`); the SMT needs those arithmetic facts spelled out.

- **`find_min_unvisited_spec_lemma` postcondition**
  - Once `unvisited_core_lemma` is fixed, this should be a thin wrapper: invoke the lemma and rewrite the quantifier to match the `is_cand` equivalence.
  - Add a short proof block that handles the empty case (`!has_unvisited_nodes`) so the forall is vacuously true.

- **`update_edges_preserves_state_inv` (rlimit + assumes)**
  - Replace the `assume` placeholders with actual sub-lemmas:
    - reuse `min_updated_distance_helper_witness` (or split it) to show each relaxed neighbor retains the upper bound and witness path,
    - and prove already-visited nodes keep exact distances.
  - Consider splitting the body by property (one lemma per invariant) to keep each VC lightweight.

Once these are in place, the file should verify cleanly again. Let me know which one you’d like to tackle first and I can walk through the details or sketch the helper lemmas.






























Here’s a route to clear the four remaining obligations:

---

### 1. `sp_dist_upper_bound_for_path` (rlimit exhaustion)

- The solver is stuck on the big `choose`/`forall`. Split the argument:
  - Write a helper `proof fn sp_dist_min_witness(graph, s, t) -> (Seq<int>)` (or a lemma returning/establishing existence) that does nothing but pick the minimal witness and prove it really is minimal.
  - Have `sp_dist_upper_bound_for_path` call that helper and then perform only the single “≤ path cost” comparison. The main lemma becomes a wrapper and no longer carries the heavy quantifier itself.
- Alternatively add `--rlimit` or `#[verifier::spinoff_exe]` style attributes, but giving the quantifier its own lemma usually drops the VC size enough to avoid the rlimit.

---

### 2. `unvisited_core_lemma` (postcondition + recommends)

The failure is because, when you assert `is_cand(dist, visited, result_node)` and the quantified postconditions, Verus can’t see:

- that the `result_node` you’re talking about is in bounds (needed for `is_cand`’s `recommends`),
- how the recursive call’s guarantees extend to the current `start_node`.

Fixing approach:

1. After computing `new_best`, call the recursion and *capture* the result:
   `let rec_res = unvisited_core(dist, visited, start_node + 1, new_best);`
2. Immediately invoke the lemma on that recursive call and match on `rec_res`. For each branch:
   - Re-establish the `0 ≤ rec_node < dist.len()` fact (and for `start_node` itself when it’s chosen).
   - Combine the recursive forall with the `start_node` case explicitly. For `j == start_node`, reason via the `is_cand` branch and `new_best`.
   - Translate `new_best`’s guarantee back to the original `best_node` (when `start_node` isn’t a candidate, `new_best == best_node`; when it is, compare using your `is_better` helper).
3. If you don’t already have them, add mini lemmas:
   - `!is_better(i, j) ==> (i == j || is_better(j, i))`
   - `is_better(i, j) && is_better(j, k) ==> is_better(i, k)`
   These let you reason about the “best” element cleanly inside the match.

Once the recursive proof is structured that way, the “recommendation not met” notes disappear.

---

### 3. `find_min_unvisited_spec_lemma`

Once `unvisited_core_lemma` is solid, this wrapper is easy: split on `has_unvisited_nodes`. In the “false” branch, the forall is vacuously true; in the “true” branch, call `unvisited_core_lemma` and massage the quantifier so the `Option::Some(i)` equality matches what the lemma proved. The current failure is purely a dependency on fixing #2.

---

### 4. `update_edges_preserves_state_inv` (rlimit and `assume`s)

Right now the proof still has `assume(...)` placeholders, so Verus punts. You need to replace those with actual arguments:

- Reuse `min_updated_distance_helper_witness` to prove that any relaxed neighbor keeps a witness path and the upper-bound property.
- Split the invariant into sub-lemmas if needed: one lemma showing distances stay upper bounds, another for `visited_nodes_have_exact_distance`, etc., each proved inductively over the adjacency list. Keeping each VC small avoids rlimit.
- For already-visited nodes, assert the old distances remain unchanged (because the spec only updates unvisited neighbors) and invoke the invariants you already have.

Make sure each sub-lemma obeys the same recommends as the parent so you can call them without triggering “recommendation not met.”

---

Once those are in place, `verus src/main.rs --triggers-mode silent` should run cleanly. Let me know which of the four you want to tackle first and I can help draft the actual proof structure.
