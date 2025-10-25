use vstd::prelude::*;

verus! {

pub struct Edge {
  pub to: usize,
  pub w: u64
}
pub struct Graph {
  pub n: usize,
  pub adj: Vec<Vec<Edge>>
}

spec fn has_correct_adjacency_length(g: Graph) -> bool {
  g.adj.len() == g.n
}

spec fn has_valid_node_bounds(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.n ==>
    (#[trigger] g.adj[u].len() >= 0) && u < g.adj.len()
}

spec fn has_valid_edge_targets(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.n ==> (
    forall|i: int| 0 <= i < #[trigger] g.adj[u].len() ==> {
      let edge = #[trigger] g.adj[u][i];
      edge.to < g.n
    }
  )
}

spec fn has_no_self_loops(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.n ==> (
    forall|i: int| 0 <= i < #[trigger] g.adj[u].len() ==> {
      let edge = #[trigger] g.adj[u][i];
      edge.to != u
    }
  )
}

spec fn has_non_negative_weights(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.n ==> (
    forall|i: int| 0 <= i < #[trigger] g.adj[u].len() ==> {
      let edge = #[trigger] g.adj[u][i];
      edge.w > 0
    }
  )
}

spec fn has_no_weight_overflow(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.n ==> (
    forall|i: int| 0 <= i < #[trigger] g.adj[u].len() ==> {
      let edge = #[trigger] g.adj[u][i];
      edge.w <= u64::MAX as int
    }
  )
}

spec fn has_no_duplicate_edges(g: Graph) -> bool {
  forall|u: int| 0 <= u < g.n ==> (
    forall|i: int, j: int|
      0 <= i < #[trigger] g.adj[u].len()
      && 0 <= j < #[trigger] g.adj[u].len()
      && i != j
      ==> (
        #[trigger] g.adj[u][i].to != #[trigger] g.adj[u][j].to
        || #[trigger] g.adj[u][i].w != #[trigger] g.adj[u][j].w
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

spec fn dijkstra_init_spec(g: Graph, s: usize) -> (Seq<Option<int>>, Seq<bool>)
{
  // TODO: Should this be a recommends? Or just keep it as a base case?
  if !is_valid(g) || !(s < g.n) {
    (Seq::empty(), Seq::empty())
  } else {
    let n: int = g.n as int;
    let dist = Seq::new(n as nat, |i:int| if i == s as int { Some(0) } else { None });
    let visited = Seq::new(n as nat, |_i:int| false);
    (dist, visited)
  }
}

spec fn shortest_path_distance_spec(g: Graph, s: usize, v: usize) -> int
{
  0
}

spec fn dijkstra_spec(g: Graph, s: usize) -> (dist: Seq<int>) {
  // TODO:
  Seq::empty()
}


pub fn run_examples() {
  // Example: Create a simple graph with 4 nodes
  // Nodes: 0, 1, 2, 3
  // Edges: 0->1 (weight 5), 0->2 (weight 3), 1->3 (weight 2), 2->3 (weight 1)
  let example_graph: Graph = Graph {
    n: 4,
    adj: vec![
      vec![Edge { to: 1, w: 5 }, Edge { to: 2, w: 3 }],
      vec![Edge { to: 3, w: 2 }],
      vec![Edge { to: 3, w: 1 }],
      vec![]
    ]
  };

  assert(is_valid(example_graph));

}

} // verus!
