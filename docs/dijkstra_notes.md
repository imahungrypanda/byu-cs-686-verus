# Dijkstra's Algorithm — High-Level Breakdown + Verification Notes

## Overview

Dijkstra's algorithm computes shortest paths from a source node to all other nodes in a weighted graph (with non-negative edge weights).

It works by expanding a frontier of known shortest paths outward one node at a time.

## Steps and Ensures

### Step 1 — Build / map out the graph

**Purpose:**
Represent all nodes, their neighbors, and edge weights.

**Representation (Rust/Verus style):**

```rust
pub struct Edge { pub to: usize, pub w: u64 }
pub struct Graph { pub n: usize, pub adj: Vec<Vec<Edge>> }
```

**Ensures / specs:**

- `g.adj.len() == g.n`
- All edge targets in range:
  `forall u,i :: 0 ≤ u < g.n ∧ 0 ≤ i < g.adj[u].len() ⇒ g.adj[u][i].to < g.n`
- All weights non-negative:
  `forall u,i :: g.adj[u][i].w ≥ 0`
- No self-contradictory or invalid references

### Step 2 — Initialize distances and visited flags

**Purpose:**
Set up the algorithm's working state.

**Initialization:**

```rust
let mut dist = vec![INF; g.n];
let mut visited = vec![false; g.n];
dist[src] = 0;
```

**Ensures / invariants:**

- `dist.len() == g.n`
- `visited.len() == g.n`
- `forall v :: dist[v] ≤ INF`
- `dist[src] == 0`
- `visited[v] == false` for all v
- `src < g.n`
- No overflow risk when adding any w to dist[u]

### Step 3 — Pick next unvisited node with minimum distance

**Purpose:**
Find the unvisited vertex with smallest current distance (u_min).

**Ensures / invariants:**

- If reachable nodes remain:
  `exists u :: !visited[u] ∧ dist[u] < INF`
- Selected node is minimal among unvisited:
  `forall v :: !visited[v] ⇒ dist[u_min] ≤ dist[v]`
- `u_min < g.n`
- If none found → all remaining unvisited nodes are unreachable (dist == INF)

### Step 4 — Mark visited and relax outgoing edges

**Purpose:**
Finalize one node, and update neighbors if you found shorter paths.

**Core logic:**

```rust
visited[u_min] = true;
for e in g.adj[u_min] {
    let v = e.to;
    let w = e.w;
    if dist[u_min] + w < dist[v] {
        dist[v] = dist[u_min] + w;
    }
}
```

**Ensures / invariants:**

- Visited grows monotonically:
  `visited_old ⊆ visited_new`
- Distance monotonicity:
  `forall v :: dist_new[v] ≤ dist_old[v]`
- Relaxation preserves correctness:
  `if dist[u]+w < dist[v] then dist[v] = dist[u]+w`
- Relaxed distances stay ≤ INF and ≤ u64::MAX
- Visited nodes never change distance again
- Key correctness fact:
  `visited[v] ⇒ dist[v] == sp_dist(g, src, v)` (once proven)

### Step 5 — Repeat until all vertices finalized

**Purpose:**
Iterate until all reachable nodes are visited or no smaller distances exist.

**Ensures / invariants:**

- Termination: measure = number of unvisited nodes decreases
- For all v, `dist[v] ≥ sp_dist(g, src, v)` (never too small)
- For all visited v, `dist[v] == sp_dist(g, src, v)` (exact)
- No more edges can improve any distance
- Return value:
  - `dist.len() == g.n`
  - `dist[src] == 0`
  - `forall v :: dist[v] ≤ INF`

## Core Algorithm Invariants (global)

1. `visited` never decreases.
2. `dist[src] == 0`.
3. `forall v :: 0 ≤ dist[v] ≤ INF`.
4. `visited[v] ⇒ dist[v] == sp_dist(g,src,v)`.
5. For all unvisited v, `dist[v]` is an upper bound on the true shortest path.
6. The count of visited vertices increases monotonically.
7. No overflow: `dist[u] + w ≤ u64::MAX`.

## Data used in proofs

| Symbol         | Meaning                                             |
| -------------- | --------------------------------------------------- |
| g              | Graph                                               |
| dist           | Current distance estimates                          |
| visited        | Boolean array of finalized vertices                 |
| src            | Source vertex                                       |
| INF            | Sentinel for infinity (e.g., 0x3f3f_3f3f_3f3f_3f3f) |
| sp_dist(g,s,v) | Spec-level true shortest-path distance              |

## Proof structure (in Verus terms)

| Concept                     | Verus construct                           |
| --------------------------- | ----------------------------------------- |
| Graph structure soundness   | `predicate wf(g)`                         |
| Shortest path definition    | `spec fn sp_dist(g,s,v) -> u64`           |
| Initialization safety       | Loop invariants on array lengths / bounds |
| Relaxation correctness      | `Lemma: relaxation_preserves_upper_bound` |
| Optimality ("cut property") | `Lemma: min_vertex_final_is_optimal`      |
| Monotonic growth            | `Invariant: visited.count() == selected`  |

## End-state guarantees

After the algorithm terminates:

- `forall v :: visited[v] ⇒ dist[v] == sp_dist(g, src, v)`
- `forall v :: dist[v] ≤ INF`
- `dist[src] == 0`
- `dist.len() == g.n`

**Meaning:**
Every reachable node has its exact shortest distance, and unreachable nodes remain at INF.

## Implementation Verification Checklist

### Graph Structure

- [x] Define `Edge` struct with `to: usize` and `w: u64`
- [x] Define `Graph` struct with `n: usize` and `adj: Vec<Vec<Edge>>`
- [x] Prove `g.adj.len() == g.n`
- [x] Prove all edge targets are in range: `forall u,i :: 0 ≤ u < g.n ∧ 0 ≤ i < g.adj[u].len() ⇒ g.adj[u][i].to < g.n`
- [x] Prove all weights non-negative: `forall u,i :: g.adj[u][i].w ≥ 0`

### Initialization

- [ ] Initialize `dist` array with INF values
- [ ] Initialize `visited` array with false values
- [ ] Set `dist[src] = 0`
- [ ] Prove array length invariants: `dist.len() == g.n` and `visited.len() == g.n`
- [ ] Prove `dist[src] == 0`
- [ ] Prove all initial distances ≤ INF
- [ ] Prove no overflow risk in distance calculations

```rust
pub exec fn dijkstra_init(g: Graph, s: usize) -> (Vec<Option<u64>>, Vec<bool>)
  requires
    is_valid(g),
    s < g.n,
  ensures
    result.0@.len() == g.n as int,
    result.1@.len() == g.n as int,
    result.0@[(s as int)] == Some(0u64),
    result.1@[(s as int)] == false,
{
  let mut dist: Vec<Option<u64> > = vec![None; g.n];
  let visited: Vec<bool> = vec![false; g.n];
  dist[s] = Some(0u64);
  (dist, visited)
}
```

### Main Loop Structure

- [ ] Implement loop to find minimum unvisited node
- [ ] Prove loop termination (number of unvisited nodes decreases)
- [ ] Prove selected node is minimal: `forall v :: !visited[v] ⇒ dist[u_min] ≤ dist[v]`
- [ ] Handle case when no reachable nodes remain

### Relaxation Step

- [ ] Mark selected node as visited
- [ ] Iterate through outgoing edges
- [ ] Update neighbor distances when shorter path found
- [ ] Prove visited set grows monotonically
- [ ] Prove distance estimates never increase
- [ ] Prove relaxation preserves upper bound property

### Correctness Proofs

- [ ] Prove `visited[v] ⇒ dist[v] == sp_dist(g, src, v)`
- [ ] Prove for unvisited v: `dist[v] ≥ sp_dist(g, src, v)`
- [ ] Prove optimality of selected minimum node
- [ ] Prove final distances are exact for all reachable nodes

### Termination and Final State

- [ ] Prove algorithm terminates
- [ ] Prove final `dist` array has correct length
- [ ] Prove `dist[src] == 0`
- [ ] Prove all distances ≤ INF
- [ ] Prove unreachable nodes remain at INF

## Quick conceptual summary

1. Map the graph → ensure valid structure
2. Initialize → safe base case (dist[src]=0)
3. Pick min unvisited → ensures progress
4. Relax neighbors → improves estimates safely
5. Repeat until done → guarantees optimal shortest paths

---

### Quantifiers and triggers (Verus tips)

- When using `forall` in specs (e.g., over `g.adj[u]`), add `#[trigger]` on terms that mention all bound vars, such as `g.adj[u].len()` and `g.adj[u][i]`.
- Example pattern used in this repo:
  ```rust
  forall|u: int| 0 <= u < g.n ==> (
      forall|i: int|
          0 <= i < #[trigger] g.adj[u].len() ==> {
              let edge = #[trigger] g.adj[u][i];
              edge.to < g.n
          }
  )
  ```
- You can acknowledge auto-chosen triggers with `#![auto]` inside the forall body.
- Reference: Verus guide on triggers: https://verus-lang.github.io/verus/guide/forall.html?highlight=trigger#forall-and-triggers
