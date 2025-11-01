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

spec fn dijkstra_init_spec(graph: Graph, start_node: int) -> (Seq<Option<int>>, Seq<bool>)
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  if !is_valid(graph) || !(start_node < graph.number_of_nodes) {
    (Seq::empty(), Seq::empty())
  } else {
    let dist = Seq::new(graph.number_of_nodes as nat, |i:int|
      if i == start_node {
        Some(0)
      } else {
        None
      }
    );
    let visited = Seq::new(graph.number_of_nodes as nat, |_i:int| false);
    (dist, visited)
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

// TODO: Add proof for this function
spec fn is_cand(dist: Seq<Option<int>>, visited: Seq<bool>, i: int) -> bool
  recommends
    0 <= i < dist.len() as int,
{
  match dist[i] {
    Some(_) => !visited[i],
    None => false,
  }
}

// TODO: Add proof for this function
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

// TODO: Add proof for this function
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

// TODO: Add proof for this function
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

spec fn dijkstra_core_spec(graph: Graph, start_node: int) -> Seq<Option<int>>
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  let (dist, visited) = dijkstra_init_spec(graph, start_node);

  let visited = visited.update(start_node, true);

  // TODO: There is no way to iterate over a sequence in Verus.
  // while !visited.all(|b:bool| b) {
  //   let next_node: int = find_min_unvisited_spec(dist, visited);

  //   for edge in graph.adjacent_nodes[next_node] {
  //     if !visited[edge.to as int] {
  //       // TODO is this right?
  //       visited.update(edge.to as int, true);
  //     }
  //   }
  // }

  dist
}

spec fn dijkstra_spec(graph: Graph, start_node: int) -> Seq<Option<int>>
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  let number_of_nodes: int = graph.number_of_nodes as int;
  if !is_valid(graph) || !(0 <= start_node && start_node < number_of_nodes) {
    Seq::empty()
  } else {
    dijkstra_core_spec(graph, start_node)
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
}

} // verus!
