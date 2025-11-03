use vstd::prelude::*;

verus! {

pub struct Edge {
  pub to: usize,
  pub w: u64
}

pub struct Graph {
  pub number_of_nodes: usize,
  pub adjacent_nodes: Vec<Vec<Edge>>
}

spec fn has_correct_adjacency_length(g: Graph) -> bool {
  g.adjacent_nodes.len() == g.number_of_nodes
}

spec fn has_valid_node_bounds(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.number_of_nodes ==>
    (#[trigger] g.adjacent_nodes[u].len() >= 0) && u < g.adjacent_nodes.len()
}

spec fn has_valid_edge_targets(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.number_of_nodes ==> (
    forall|i: int| 0 <= i < #[trigger] g.adjacent_nodes[u].len() ==> {
      let edge: Edge = #[trigger] g.adjacent_nodes[u][i];
      edge.to < g.number_of_nodes
    }
  )
}

spec fn has_no_self_loops(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.number_of_nodes ==> (
    forall|i: int| 0 <= i < #[trigger] g.adjacent_nodes[u].len() ==> {
      let edge: Edge = #[trigger] g.adjacent_nodes[u][i];
      edge.to != g.number_of_nodes
    }
  )
}

spec fn has_non_negative_weights(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.number_of_nodes ==> (
    forall|i: int| 0 <= i < #[trigger] g.adjacent_nodes[u].len() ==> {
      let edge: Edge = #[trigger] g.adjacent_nodes[u][i];
      edge.w > 0
    }
  )
}

spec fn has_no_weight_overflow(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.number_of_nodes ==> (
    forall|i: int| 0 <= i < #[trigger] g.adjacent_nodes[u].len() ==> {
      let edge: Edge = #[trigger] g.adjacent_nodes[u][i];
      edge.w <= u64::MAX as int
    }
  )
}

spec fn has_no_duplicate_edges(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.number_of_nodes ==> (
    forall|i: int, j: int|
      0 <= i < #[trigger] g.adjacent_nodes[u].len()
      && 0 <= j < #[trigger] g.adjacent_nodes[u].len()
      && i != j
      ==> (
        #[trigger] g.adjacent_nodes[u][i].to != #[trigger] g.adjacent_nodes[u][j].to
        || #[trigger] g.adjacent_nodes[u][i].w != #[trigger] g.adjacent_nodes[u][j].w
      )
  )
}

// Graph validition
spec fn is_valid(g: Graph) -> bool {
  has_correct_adjacency_length(g)
    && has_valid_node_bounds(g)
    && has_valid_edge_targets(g)
    && has_no_self_loops(g)
    && has_non_negative_weights(g)
    && has_no_weight_overflow(g)
    && has_no_duplicate_edges(g)
}

spec fn dijkstra_init_spec(graph: Graph, start_node: int) -> Seq<Option<int>>
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  if !is_valid(graph) || !(start_node < graph.number_of_nodes) {
    Seq::empty()
  } else {
    Seq::new(graph.number_of_nodes as nat, |_i:int| false);
  }
}

spec fn has_unvisited_nodes(dist: Seq<Option<int>>, visited: Seq<bool>) -> bool
  recommends
    dist.len() == visited.len() as int,
{
  exists|i: int| 0 <= i && i < dist.len() as int && !visited[i] && dist[i] matches Some(_)
}

proof fn has_unvisited_nodes_lemma(dist: Seq<Option<int>>, visited: Seq<bool>) -> bool
  requires
    dist.len() == visited.len() as int,
  ensures
    exists|i: int| 0 <= i < dist.len() as int && !visited[i] && dist[i] matches Some(_)
{
  exists|i: int| 0 <= i < dist.len() as int && !visited[i] && dist[i] matches Some(_)
}

pub fn has_unvisited_nodes_proof_tests() {
  proof {
    // Test case 1: Has unvisited nodes with distances
    let dist = seq![Some(0), Some(5), None, Some(3)];
    let visited = seq![true, false, false, false];
    assert(dist.len() == visited.len() as int);
    assert(has_unvisited_nodes(dist, visited));

    // Test case 2: All nodes visited
    let dist = seq![Some(0), Some(5), Some(3)];
    let visited = seq![true, true, true];
    assert(dist.len() == visited.len() as int);
    assert(!has_unvisited_nodes(dist, visited));

    // Test case 3: Unvisited nodes but no distances
    let dist = seq![Some(0), None, None];
    let visited = seq![true, false, false];
    assert(dist.len() == visited.len() as int);
    assert(!has_unvisited_nodes(dist, visited));

    // Test case 4: Empty sequences
    let dist = Seq::empty();
    let visited = Seq::empty();
    assert(dist.len() == visited.len() as int);
    assert(!has_unvisited_nodes(dist, visited));

    // Test case 5: Single unvisited node with distance
    let dist = seq![Some(0)];
    let visited = seq![false];
    assert(dist.len() == visited.len() as int);
    assert(has_unvisited_nodes(dist, visited)) by {
      assert(dist[0] matches Some(_));
      assert(!visited[0]);
    };
  }
}

// Is this node a candidate for the next node to visit?
spec fn is_cand(dist: Seq<Option<int>>, visited: Seq<bool>, i: int) -> bool
  recommends
    0 <= i < dist.len() as int,
{
  match dist[i] {
    Some(_) => !visited[i],
    None => false,
  }
}

proof fn is_cand_lemma(dist: Seq<Option<int>>, visited: Seq<bool>, i: int)
  requires
    0 <= i < dist.len() as int,
    dist.len() == visited.len() as int,
  ensures
    is_cand(dist, visited, i) <==> (dist[i] matches Some(_) && !visited[i])
{
  if dist[i] matches Some(_) {
    assert(is_cand(dist, visited, i) == !visited[i]);
    assert((dist[i] matches Some(_) && !visited[i]) == !visited[i]);
    assert(is_cand(dist, visited, i) == (dist[i] matches Some(_) && !visited[i]));
  } else {
    assert(is_cand(dist, visited, i) == false);
    assert((dist[i] matches Some(_) && !visited[i]) == false);
    assert(is_cand(dist, visited, i) == (dist[i] matches Some(_) && !visited[i]));
  }
}

pub fn is_cand_proof_tests() {
  proof {
    let dist = seq![Some(0), Some(5), None, Some(3)];
    let visited = seq![true, false, false, false];

    // Test case 1: Node with distance and not visited (should be true)
    assert(is_cand(dist, visited, 1));  // node 1: Some(5), not visited

    // Test case 2: Node with distance but already visited (should be false)
    assert(!is_cand(dist, visited, 0));  // node 0: Some(0), but visited

    // Test case 3: Node with no distance (None) - not visited (should be false)
    assert(!is_cand(dist, visited, 2));  // node 2: None, not visited

    // Test case 4: Node with no distance (None) - visited (should be false)
    let dist_2 = seq![Some(0), None, Some(3)];
    let visited_2 = seq![true, true, false];
    assert(!is_cand(dist_2, visited_2, 1));  // node 1: None, visited

    // Test case 5: Node with distance and not visited at end of sequence
    assert(is_cand(dist, visited, 3));  // node 3: Some(3), not visited

    // Test case 6: All nodes have distances, one not visited
    let dist_3 = seq![Some(0), Some(5), Some(3)];
    let visited_3 = seq![true, false, true];
    assert(is_cand(dist_3, visited_3, 1));  // node 1: Some(5), not visited
    assert(!is_cand(dist_3, visited_3, 0)); // node 0: Some(0), visited
    assert(!is_cand(dist_3, visited_3, 2)); // node 2: Some(3), visited

    // Test case 7: All nodes have None (no distances)
    let dist_4 = seq![None, None, None];
    let visited_4 = seq![false, false, false];
    assert(!is_cand(dist_4, visited_4, 0));  // node 0: None
    assert(!is_cand(dist_4, visited_4, 1));  // node 1: None
  }
}

spec fn is_better(dist: Seq<Option<int>>, start_node: int, new_node: int) -> bool
  recommends
    0 <= start_node < dist.len() as int,
    0 <= new_node < dist.len() as int,
    dist[start_node] matches Some(_),
    dist[new_node] matches Some(_)
{
  match (dist[start_node], dist[new_node]) {
    (Some(di), Some(db)) => di < db || (di == db && start_node <= new_node),
    _ => false,
  }
}

// Lemma characterizing is_better: it's true iff start_node has smaller distance,
// or equal distance with start_node <= new_node
// NOTE: Ties are broken by the start_node <= new_node condition.
proof fn is_better_lemma(dist: Seq<Option<int>>, start_node: int, new_node: int)
  requires
    0 <= start_node < dist.len() as int,
    0 <= new_node < dist.len() as int,
    dist[start_node] matches Some(_),
    dist[new_node] matches Some(_),
  ensures
    is_better(dist, start_node, new_node) <==>
      (match (dist[start_node], dist[new_node]) {
        (Some(di), Some(db)) => di < db || (di == db && start_node <= new_node),
        _ => false,
      })
{
  match dist[start_node] {
    Some(di) => {
      match dist[new_node] {
        Some(db) => {
          // Case analysis: di < db, di == db, or di > db
          if di < db {
            // Case 1: di < db, so is_better is true
            assert(is_better(dist, start_node, new_node) == true);
            assert((di < db || (di == db && start_node <= new_node)) == true);
            assert(is_better(dist, start_node, new_node) == (di < db || (di == db && start_node <= new_node)));
          } else if di == db {
            // Case 2: di == db, so is_better depends on start_node <= new_node
            assert(is_better(dist, start_node, new_node) == (start_node <= new_node));
            assert((di < db || (di == db && start_node <= new_node)) == (start_node <= new_node));
            assert(is_better(dist, start_node, new_node) == (di < db || (di == db && start_node <= new_node)));
          } else {
            // Case 3: di > db, so is_better is false
            assert(is_better(dist, start_node, new_node) == false);
            assert((di < db || (di == db && start_node <= new_node)) == false);
            assert(is_better(dist, start_node, new_node) == (di < db || (di == db && start_node <= new_node)));
          }
        }
        None => {}
      }
    }
    None => {}
  }
}

pub fn is_better_proof_tests() {
  proof {
    // Test case 1: start_node has smaller distance (should be true)
    let dist = seq![Some(0), Some(5), Some(10), Some(3)];
    assert(is_better(dist, 0, 1));  // dist[0]=0 < dist[1]=5

    // Test case 2: start_node has larger distance (should be false)
    assert(!is_better(dist, 1, 0));  // dist[1]=5 > dist[0]=0

    // Test case 3: Equal distances, start_node < new_node (should be true)
    let dist_2 = seq![Some(5), Some(5), Some(5)];
    assert(is_better(dist_2, 0, 1));  // dist[0]=5 == dist[1]=5, and 0 <= 1

    // Test case 4: Equal distances, start_node == new_node (should be true)
    assert(is_better(dist_2, 0, 0));  // dist[0]=5 == dist[0]=5, and 0 <= 0

    // Test case 5: Equal distances, start_node > new_node (should be false)
    assert(!is_better(dist_2, 2, 1));  // dist[2]=5 == dist[1]=5, but 2 > 1

    // Test case 6: start_node much smaller distance
    let dist_3 = seq![Some(1), Some(100)];
    assert(is_better(dist_3, 0, 1));  // dist[0]=1 < dist[1]=100

    // Test case 7: start_node much larger distance
    assert(!is_better(dist_3, 1, 0));  // dist[1]=100 > dist[0]=1

    // Test case 8: Multiple equal distances, checking tie-breaking
    let dist_4 = seq![Some(7), Some(7), Some(7), Some(7)];
    assert(is_better(dist_4, 0, 3));  // dist[0]=7 == dist[3]=7, and 0 <= 3
    assert(!is_better(dist_4, 3, 0));  // dist[3]=7 == dist[0]=7, but 3 > 0
  }
}

spec fn unvisited_core(dist: Seq<Option<int>>, visited: Seq<bool>, start_node: int, best_node: Option<int>) -> Option<int>
  recommends
    dist.len() == visited.len(),
    0 <= start_node <= dist.len() as int,
    best_node matches Some(_) ==> best_node.unwrap() < dist.len() as int,
  decreases
    dist.len() - start_node
{
  let dist_len = dist.len() as int;
  let visited_len = visited.len() as int;

  if start_node < 0 || start_node >= dist_len || start_node >= visited_len {
    best_node
  } else {
    let new_best: Option<int> = if is_cand(dist, visited, start_node) {
      match best_node {
        Option::None => Option::Some(start_node),
        Option::Some(test_node) =>
          if is_better(dist, start_node, test_node) {
            Option::Some(start_node)
          } else {
            best_node
          }
      }
    } else {
      best_node
    };

    unvisited_core(dist, visited, start_node + 1, new_best)
  }
}

// Lemma characterizing unvisited_core: returns the best candidate from start_node onward
// If result is Some(i), then i is a candidate and is better than or equal to all other
// candidates from start_node onward, and better than or equal to best_node (if best_node is Some)
proof fn unvisited_core_lemma(dist: Seq<Option<int>>, visited: Seq<bool>, start_node: int, best_node: Option<int>)
  requires
    dist.len() == visited.len(),
    0 <= start_node <= dist.len() as int,
    best_node matches Some(_) ==> best_node.unwrap() < dist.len() as int,
  ensures
    match unvisited_core(dist, visited, start_node, best_node) {
      Option::Some(result_node) =>
        is_cand(dist, visited, result_node) &&
        (forall|j: int| start_node <= j && j < dist.len() as int && is_cand(dist, visited, j) ==>
          result_node == j || is_better(dist, result_node, j)) &&
        (best_node matches Option::Some(best) ==>
          result_node == best || is_better(dist, result_node, best)),
      Option::None =>
        !exists|j: int| start_node <= j && j < dist.len() as int && is_cand(dist, visited, j) &&
        (best_node == Option::None || !is_cand(dist, visited, best_node.unwrap()))
    }
  decreases
    dist.len() - start_node
{
  // Base case: start_node is out of bounds
  if start_node < 0 || start_node >= dist.len() as int || start_node >= visited.len() as int {
    // Returns best_node directly
    match best_node {
      Option::Some(best) => {
        // Since start_node >= dist.len(), there are no candidates j where start_node <= j < dist.len()
        // So the forall is vacuously true (no such j exist)
        // Also, result_node == best, so the condition "result_node == best || is_better(dist, result_node, best)" holds
        assert(forall|j: int| start_node <= j && j < dist.len() as int && is_cand(dist, visited, j) ==>
          best == j || is_better(dist, best, j));
        assert(best == best || is_better(dist, best, best));
      }
      Option::None => {
        // Since start_node >= dist.len(), there are no candidates j where start_node <= j < dist.len()
        // So !exists|j| start_node <= j < dist.len() && is_cand(dist, visited, j) is true
        // And best_node == Option::None is true
        assert(!exists|j: int| start_node <= j && j < dist.len() as int && is_cand(dist, visited, j));
        assert(best_node == Option::None);
      }
    }
  } else {
    // Recursive case: check if start_node is a candidate
    let new_best: Option<int> = if is_cand(dist, visited, start_node) {
      match best_node {
        Option::None => Option::Some(start_node),
        Option::Some(test_node) =>
          if is_better(dist, start_node, test_node) {
            Option::Some(start_node)
          } else {
            best_node
          }
      }
    } else {
      best_node
    };

    unvisited_core_lemma(dist, visited, start_node + 1, new_best);
  }
}

pub fn unvisited_core_proof_tests() {
  proof {
    // Test case 1: Base case - start_node >= dist.len(), returns best_node
    let dist = seq![Some(0), Some(5)];
    let visited = seq![false, false];
    let result: Option<int> = unvisited_core(dist, visited, 2, Option::Some(1));
    assert(result == Option::Some(1));  // Returns the passed best_node

    // Test case 2: Single candidate, starting from beginning with None
    let result_2: Option<int> = unvisited_core(dist, visited, 0, Option::None);
    assert(result_2 == Option::Some(0));  // Finds node 0 (distance 0)

    // Test case 3: Multiple candidates, finds the best (smallest distance)
    let dist_2 = seq![Some(5), Some(2), Some(8), Some(1)];
    let visited_2 = seq![false, false, false, false];
    let result_3: Option<int> = unvisited_core(dist_2, visited_2, 0, Option::None);
    assert(result_3 == Option::Some(3));  // Node 3 has smallest distance (1)

    // Test case 4: Multiple candidates with equal distances, picks smallest index
    let dist_3 = seq![Some(5), Some(5), Some(5)];
    let visited_3 = seq![false, false, false];
    let result_4: Option<int> = unvisited_core(dist_3, visited_3, 0, Option::None);
    assert(result_4 == Option::Some(0));  // Tie broken by index, picks 0

    // Test case 5: Starting from middle, finds best remaining
    let dist_4 = seq![Some(10), Some(5), Some(3), Some(7)];
    let visited_4 = seq![false, false, false, false];
    let result_5: Option<int> = unvisited_core(dist_4, visited_4, 2, Option::None);
    assert(result_5 == Option::Some(2));  // Starting from index 2, finds itself (distance 3)

    // Test case 6: All visited, returns None if starting with None
    let dist_5 = seq![Some(0), Some(5), Some(3)];
    let visited_5 = seq![true, true, true];
    let result_6: Option<int> = unvisited_core(dist_5, visited_5, 0, Option::None);
    assert(result_6 == Option::None);  // No candidates found

    // Test case 7: All have no distances (None), returns None
    let dist_6 = seq![None, None, None];
    let visited_6 = seq![false, false, false];
    let result_7: Option<int> = unvisited_core(dist_6, visited_6, 0, Option::None);
    assert(result_7 == Option::None);  // No candidates (no distances)

    // Test case 8: Mix of visited/unvisited, finds unvisited candidate
    let dist_7 = seq![Some(0), Some(5), Some(3)];
    let visited_7 = seq![true, false, false];
    let result_8: Option<int> = unvisited_core(dist_7, visited_7, 0, Option::None);
    assert(result_8 == Option::Some(2));  // Node 2 has smallest distance among unvisited

    // Test case 9: Starting with existing best_node, finds better one
    let dist_8 = seq![Some(10), Some(5), Some(3)];
    let visited_8 = seq![false, false, false];
    let result_9: Option<int> = unvisited_core(dist_8, visited_8, 1, Option::Some(0));
    assert(result_9 == Option::Some(2));  // Starts with node 0 (distance 10), finds better: node 2 (distance 3)

    // Test case 10: Starting with best_node, keeps it if no better found
    let dist_9 = seq![Some(2), Some(5), Some(8)];
    let visited_9 = seq![false, false, false];
    let result_10: Option<int> = unvisited_core(dist_9, visited_9, 1, Option::Some(0));
    assert(result_10 == Option::Some(0));  // Starts with node 0 (distance 2), no better found

    // Test case 11: Empty sequences
    let dist_empty = Seq::empty();
    let visited_empty = Seq::empty();
    let result_11: Option<int> = unvisited_core(dist_empty, visited_empty, 0, Option::None);
    assert(result_11 == Option::None);  // Base case immediately returns None
  }
}

spec fn find_min_unvisited_spec(dist: Seq<Option<int>>, visited: Seq<bool>) -> Option<int>
  recommends
    dist.len() == visited.len() as int,
    has_unvisited_nodes(dist, visited),
{
  if !has_unvisited_nodes(dist, visited) {
    Option::None
  } else {
    unvisited_core(dist, visited, 0, Option::None)
  }
}

// Lemma characterizing find_min_unvisited_spec: returns the best unvisited candidate if one exists
proof fn find_min_unvisited_spec_lemma(dist: Seq<Option<int>>, visited: Seq<bool>)
  requires
    dist.len() == visited.len() as int,
    has_unvisited_nodes(dist, visited),
  ensures
    match find_min_unvisited_spec(dist, visited) {
      Option::Some(result_node) =>
        is_cand(dist, visited, result_node) &&
        (forall|j: int| 0 <= j && j < dist.len() as int && is_cand(dist, visited, j) ==>
          result_node == j || is_better(dist, result_node, j)),
      Option::None =>
        false  // Should never happen since has_unvisited_nodes is true
    }
{
  // find_min_unvisited_spec calls unvisited_core(dist, visited, 0, Option::None)
  // Use unvisited_core_lemma to get the properties
  unvisited_core_lemma(dist, visited, 0, Option::None);

  // Since has_unvisited_nodes(dist, visited) is true, there exists at least one candidate
  // So the result should be Some(i) for some candidate i
  // The unvisited_core_lemma ensures that if result is Some(i), then i is the best candidate
}

pub fn find_min_unvisited_spec_proof_tests() {
  proof {
    // Test case 1: Has unvisited nodes, finds the one with smallest distance
    let dist = seq![Some(5), Some(2), Some(8), Some(1)];
    let visited = seq![false, false, false, false];
    let result: Option<int> = find_min_unvisited_spec(dist, visited);
    assert(result == Option::Some(3));  // Node 3 has smallest distance (1)

    // Test case 2: Has unvisited nodes, equal distances pick smallest index
    let dist_2 = seq![Some(5), Some(5), Some(5)];
    let visited_2 = seq![false, false, false];
    let result_2: Option<int> = find_min_unvisited_spec(dist_2, visited_2);
    assert(result_2 == Option::Some(0));  // Tie broken by index, picks 0

    // Test case 3: All nodes visited, returns None
    let dist_3 = seq![Some(0), Some(5), Some(3)];
    let visited_3 = seq![true, true, true];
    let result_3: Option<int> = find_min_unvisited_spec(dist_3, visited_3);
    assert(result_3 == Option::None);  // No unvisited nodes

    // Test case 4: Mix of visited/unvisited, finds best unvisited
    let dist_4 = seq![Some(0), Some(5), Some(3), Some(2)];
    let visited_4 = seq![true, false, false, false];
    let result_4: Option<int> = find_min_unvisited_spec(dist_4, visited_4);
    assert(result_4 == Option::Some(3));  // Node 3 has smallest distance (2) among unvisited

    // Test case 5: Some nodes have no distances, finds best among those with distances
    let dist_5 = seq![Some(5), None, Some(3), None];
    let visited_5 = seq![false, false, false, false];
    let result_5: Option<int> = find_min_unvisited_spec(dist_5, visited_5);
    assert(result_5 == Option::Some(2));  // Node 2 has distance 3, better than node 0's 5

    // Test case 6: Only one unvisited node
    let dist_6 = seq![Some(0), Some(5), Some(3)];
    let visited_6 = seq![true, true, false];
    let result_6: Option<int> = find_min_unvisited_spec(dist_6, visited_6);
    assert(result_6 == Option::Some(2));  // Only node 2 is unvisited

    // Test case 7: All nodes have no distances, returns None
    let dist_7 = seq![None, None, None];
    let visited_7 = seq![false, false, false];
    let result_7: Option<int> = find_min_unvisited_spec(dist_7, visited_7);
    assert(result_7 == Option::None);  // No candidates (no distances)

    // Test case 8: Large distances, finds smallest
    let dist_8 = seq![Some(100), Some(50), Some(200), Some(25)];
    let visited_8 = seq![false, false, false, false];
    let result_8: Option<int> = find_min_unvisited_spec(dist_8, visited_8);
    assert(result_8 == Option::Some(3));  // Node 3 has smallest distance (25)

    // Test case 9: Single node, unvisited
    let dist_9 = seq![Some(0)];
    let visited_9 = seq![false];
    let result_9: Option<int> = find_min_unvisited_spec(dist_9, visited_9);
    assert(result_9 == Option::Some(0));  // Only node, unvisited

    // Test case 10: Single node, visited
    let dist_10 = seq![Some(0)];
    let visited_10 = seq![true];
    let result_10: Option<int> = find_min_unvisited_spec(dist_10, visited_10);
    assert(result_10 == Option::None);  // Only node is visited
  }
}

spec fn dijkstra_core_spec(graph: Graph, visited: Seq<bool>, start_node: int, destination_node: int) -> Seq<Option<int>>
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  let next_node: int = find_min_unvisited_spec(destination_node, visited);
  if next_node == destination_node {
    return next_node
  }

  // let visited = visited.update(next_node, true);
  // let dist = dist.update(next_node, Some(0));

  // TODO: How to update the path values?

  // dijkstra_core_spec(graph, visited, start_node, destination_node)

  Seq::empty()
}

spec fn dijkstra_spec(graph: Graph, start_node: int, destination_node: int) -> Seq<Option<int>>
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  let number_of_nodes: int = graph.number_of_nodes as int;
  let visited = dijkstra_init_spec(graph, start_node);
  let visited = visited.update(start_node, true);

  if !is_valid(graph) || !(0 <= start_node && start_node < number_of_nodes) {
    Seq::empty()
  } else {
    dijkstra_core_spec(graph, visited, start_node, destination_node)
  }
}

pub fn run_examples() {
  // Example: Create a simple graph with 4 nodes
  // Nodes: 0, 1, 2, 3
  // Edges: 0->1 (weight 5), 0->2 (weight 3), 1->3 (weight 2), 2->3 (weight 1)
  let example_graph: Graph = Graph {
    number_of_nodes: 4,
    adjacent_nodes: vec![
      vec![Edge { to: 1, w: 5 }, Edge { to: 2, w: 3 }],
      vec![Edge { to: 3, w: 2 }],
      vec![Edge { to: 3, w: 1 }],
      vec![]
    ]
  };

  assert(is_valid(example_graph));

  has_unvisited_nodes_proof_tests();
  unvisited_core_proof_tests();
  is_better_proof_tests();
  is_cand_proof_tests();
  has_unvisited_nodes_proof_tests();
}

} // verus!
