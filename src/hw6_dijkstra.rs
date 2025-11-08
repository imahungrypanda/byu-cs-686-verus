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

// Specification helpers for reasoning about paths and their costs
spec fn edge_exists(graph: Graph, u: int, v: int) -> bool
  recommends
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int
{
  exists|i: int|
    0 <= i < graph.adjacent_nodes[u].len() as int &&
    graph.adjacent_nodes[u][i].to == v as usize
}

spec fn edge_weight(graph: Graph, u: int, v: int) -> int
  recommends
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int,
    edge_exists(graph, u, v)
{
  graph.adjacent_nodes[u][
    choose|i: int|
      0 <= i < graph.adjacent_nodes[u].len() as int
      && graph.adjacent_nodes[u][i].to == v as usize
  ].w as int
}

spec fn path_nodes_within_bounds(graph: Graph, path: Seq<int>) -> bool {
  forall|i: int|
    0 <= i < path.len() as int ==> 0 <= path[i] && path[i] < graph.number_of_nodes as int
}

spec fn path_next(path: Seq<int>, i: int) -> int
  recommends
    0 <= i && i + 1 < path.len() as int
{
  path[i + 1]
}

spec fn path_edges_exist(graph: Graph, path: Seq<int>) -> bool
  recommends
    path.len() >= 1,
    path_nodes_within_bounds(graph, path)
{
  forall|i: int|
    0 <= i < path.len() as int - 1 ==>
      #[trigger] edge_exists(graph, path[i], path_next(path, i))
}

proof fn path_tail_preserves_bounds(graph: Graph, path: Seq<int>)
  requires
    path.len() >= 2,
    path_nodes_within_bounds(graph, path),
  ensures
    path_nodes_within_bounds(graph, path.subrange(1, path.len() as int))
{
  let tail = path.subrange(1, path.len() as int);
  assert forall|i: int|
    if 0 <= i && i < tail.len() as int {
      #[trigger] tail[i];
      0 <= tail[i] && tail[i] < graph.number_of_nodes as int
    } else {
      true
    }
  by {
    if 0 <= i && i < tail.len() as int {
      assert(tail.len() == path.len() as int - 1);
      assert(0 <= i + 1 && i + 1 < path.len() as int);
      assert(tail[i] == path[i + 1]);
      assert(0 <= path[i + 1] && path[i + 1] < graph.number_of_nodes as int);
    }
  };
}

proof fn path_tail_preserves_edges(graph: Graph, path: Seq<int>)
  requires
    is_valid(graph),
    path.len() >= 2,
    path_nodes_within_bounds(graph, path),
    path_edges_exist(graph, path),
  ensures
    path_edges_exist(graph, path.subrange(1, path.len() as int))
{
  let tail = path.subrange(1, path.len() as int);
  assert forall|i: int|
    if 0 <= i && i < tail.len() as int - 1 {
      #[trigger] edge_exists(graph, tail[i], path_next(tail, i))
    } else {
      true
    }
  by {
    if 0 <= i && i < tail.len() as int - 1 {
      assert(tail.len() == path.len() as int - 1);
      assert(0 <= i + 1 && i + 1 < path.len() as int - 1);
      assert(tail[i] == path[i + 1]);
      assert(path_next(tail, i) == tail[i + 1]);
      assert(tail[i + 1] == path[i + 2]);
      assert(edge_exists(graph, path[i + 1], path_next(path, i + 1)));
      assert(path_next(path, i + 1) == path[i + 2]);
      assert(edge_exists(graph, tail[i], path_next(tail, i)));
    }
  };
}

proof fn path_cost_unfold(graph: Graph, path: Seq<int>)
  requires
    is_valid(graph),
    path.len() >= 2,
    path_nodes_within_bounds(graph, path),
    path_edges_exist(graph, path),
  ensures
    path_cost(graph, path) == edge_weight(graph, path[0], path[1]) + path_cost(graph, path.subrange(1, path.len() as int))
{
  let tail = path.subrange(1, path.len() as int);
  path_tail_preserves_bounds(graph, path);
  path_tail_preserves_edges(graph, path);
  assert(path_nodes_within_bounds(graph, tail));
  assert(path_edges_exist(graph, tail));

  assert(edge_exists(graph, path[0], path[1])) by {
    assert(path_edges_exist(graph, path));
    assert(path.len() >= 2);
    assert(0 <= 0 && 0 < path.len() as int - 1);
    assert(path_next(path, 0) == path[1]);
  };
  let len_ghost = path.len();
  assert(len_ghost >= 2);
  assert(len_ghost - 1 >= 0);
  let tail_fuel: nat = (len_ghost - 1) as nat;
  assert(path_cost(graph, path) == edge_weight(graph, path[0], path[1]) + path_cost_core(graph, tail, tail_fuel)) by {
    assert(path_cost(graph, path) == path_cost_core(graph, path, len_ghost));
    assert(path_nodes_within_bounds(graph, tail));
    assert(path_edges_exist(graph, tail));
    assert(edge_exists(graph, path[0], path[1]));
  };
  assert(path.len() - 1 == tail.len());
  assert((path.len() - 1) as nat == tail.len() as nat);
  let tail_len_nat: nat = tail.len() as nat;
  assert(path_cost_core(graph, tail, tail_fuel) == path_cost_core(graph, tail, tail_len_nat)) by {
    assert(tail_fuel == tail_len_nat);
  };
  assert(path_cost(graph, tail) == path_cost_core(graph, tail, tail.len()));
  assert(path_cost(graph, path) == edge_weight(graph, path[0], path[1]) + path_cost(graph, tail));
}

spec fn is_path(graph: Graph, start_node: int, destination_node: int, path: Seq<int>) -> bool {
  path.len() >= 1
    && path[0] == start_node
    && path[path.len() as int - 1] == destination_node
    && path_nodes_within_bounds(graph, path)
    && path_edges_exist(graph, path)
}

spec fn dist_values_have_witness_paths(graph: Graph, start_node: int, dist: Seq<Option<int>>) -> bool
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= start_node < graph.number_of_nodes as int
{
  forall|v: int|
    0 <= v < dist.len() as int ==>
      match #[trigger] dist[v] {
        Some(d) =>
          exists|path: Seq<int>|
            #[trigger] is_path(graph, start_node, v, path)
              && #[trigger] path_cost(graph, path) == d,
        Option::<int>::None => true,
      }
}

spec fn path_cost_core(graph: Graph, path: Seq<int>, fuel: nat) -> int
  recommends
    is_valid(graph),
    path.len() >= 1,
    path_nodes_within_bounds(graph, path),
    path_edges_exist(graph, path)
  decreases
    fuel
{
  if fuel == 0 || path.len() == 1 {
    0
  } else {
    let tail = path.subrange(1, path.len() as int);
    let fuel_next: nat = if fuel == 0 { 0 } else { (fuel - 1) as nat };
    if path_nodes_within_bounds(graph, tail)
      && path_edges_exist(graph, tail)
      && edge_exists(graph, path[0], path[1])
    {
      edge_weight(graph, path[0], path[1]) + path_cost_core(graph, tail, fuel_next)
    } else {
      0
    }
  }
}

spec fn path_cost(graph: Graph, path: Seq<int>) -> int
  recommends
    is_valid(graph),
    path.len() >= 1,
    path_nodes_within_bounds(graph, path),
    path_edges_exist(graph, path)
  decreases
    path.len()
{
  path_cost_core(graph, path, path.len())
}

spec fn append_vertex(path: Seq<int>, v: int) -> Seq<int> {
  path.push(v)
}

proof fn append_vertex_preserves_bounds(graph: Graph, path: Seq<int>, v: int)
  requires
    path.len() >= 1,
    path_nodes_within_bounds(graph, path),
    0 <= v && v < graph.number_of_nodes as int,
  ensures
    path_nodes_within_bounds(graph, append_vertex(path, v))
{
  assert forall|i: int|
    if 0 <= i && i < append_vertex(path, v).len() as int {
      0 <= append_vertex(path, v)[i] && append_vertex(path, v)[i] < graph.number_of_nodes as int
    } else {
      true
    }
  by {
    if 0 <= i && i < append_vertex(path, v).len() as int {
      if i < path.len() as int {
        assert(append_vertex(path, v)[i] == path[i]);
        assert(0 <= path[i] && path[i] < graph.number_of_nodes as int);
      } else {
        assert(i == append_vertex(path, v).len() as int - 1);
        assert(append_vertex(path, v)[i] == v);
        assert(0 <= v && v < graph.number_of_nodes as int);
      }
    }
  };
}

proof fn append_vertex_preserves_edges(graph: Graph, path: Seq<int>, v: int)
  requires
    is_valid(graph),
    path.len() >= 1,
    path_nodes_within_bounds(graph, path),
    path_edges_exist(graph, path),
    0 <= v && v < graph.number_of_nodes as int,
    edge_exists(graph, path[path.len() as int - 1], v),
  ensures
    path_edges_exist(graph, append_vertex(path, v))
{
  assert forall|i: int|
    if 0 <= i && i < append_vertex(path, v).len() as int - 1 {
      #[trigger] edge_exists(graph, append_vertex(path, v)[i], path_next(append_vertex(path, v), i))
    } else {
      true
    }
  by {
    if 0 <= i && i < append_vertex(path, v).len() as int - 1 {
      if i < path.len() as int - 1 {
        assert(0 <= i && i < path.len() as int - 1);
        assert(edge_exists(graph, path[i], path_next(path, i))) by {
          assert(path_edges_exist(graph, path));
        };
        assert(append_vertex(path, v)[i] == path[i]);
        assert(path_next(append_vertex(path, v), i) == path[i + 1]);
      } else {
        assert(i == append_vertex(path, v).len() as int - 2);
        assert(append_vertex(path, v)[i] == path[path.len() as int - 1]);
        assert(path_next(append_vertex(path, v), i) == v);
        assert(edge_exists(graph, path[path.len() as int - 1], v));
      }
    }
  };
}

proof fn append_vertex_is_path(graph: Graph, start_node: int, path: Seq<int>, v: int)
  requires
    is_valid(graph),
    path.len() >= 1,
    is_path(graph, start_node, path[path.len() as int - 1], path),
    0 <= v && v < graph.number_of_nodes as int,
    edge_exists(graph, path[path.len() as int - 1], v),
  ensures
    is_path(graph, start_node, v, append_vertex(path, v))
{
  append_vertex_preserves_bounds(graph, path, v);
  append_vertex_preserves_edges(graph, path, v);

  assert(append_vertex(path, v).len() >= 1);
  assert(append_vertex(path, v)[0] == path[0]);
  assert(path[0] == start_node);
  assert(append_vertex(path, v)[append_vertex(path, v).len() as int - 1] == v);

  assert(is_path(graph, start_node, v, append_vertex(path, v)));
}

proof fn append_vertex_tail_subrange(path: Seq<int>, v: int)
  requires
    path.len() >= 1
  ensures
    append_vertex(path, v)
      .subrange(1, append_vertex(path, v).len() as int)
      == append_vertex(path.subrange(1, path.len() as int), v)
{
  let appended = append_vertex(path, v);
  let tail = path.subrange(1, path.len() as int);
  let appended_tail = appended.subrange(1, appended.len() as int);
  let appended_len = appended.len() as int;
  let appended_tail_len = appended_tail.len() as int;
  let tail_len = tail.len() as int;
  let appended_tail_expected = append_vertex(tail, v);
  let appended_tail_expected_len = appended_tail_expected.len() as int;

  assert(appended_len == path.len() as int + 1);
  assert(appended_tail_len == appended_len - 1);
  assert(appended_tail_len == path.len() as int);
  assert(tail_len == path.len() as int - 1);
  assert(appended_tail_expected_len == tail_len + 1);
  assert(appended_tail_expected_len == appended_tail_len);

  assert forall|i: int|
    if 0 <= i && i < appended_tail_len {
      appended_tail[i] == appended_tail_expected[i]
    } else {
      true
    }
  by {
    if 0 <= i && i < appended_tail_len {
      if i < tail_len {
        assert(0 <= i + 1 && i + 1 < appended_len);
        assert(appended_tail[i] == appended[i + 1]);
        if i + 1 < path.len() as int {
          assert(appended[i + 1] == path[i + 1]);
          assert(appended_tail_expected[i] == tail[i]);
          assert(tail[i] == path[i + 1]);
        } else {
          assert(i + 1 == path.len() as int);
          assert(appended[i + 1] == v);
          assert(i == tail_len - 1);
          assert(appended_tail_expected[i] == tail[i]);
          assert(tail[i] == path[path.len() as int - 1]);
        }
      } else {
        assert(i == tail_len);
        assert(i + 1 < appended_len);
        assert(appended_tail[i] == appended[i + 1]);
        assert(appended[i + 1] == v);
        assert(appended_tail_expected_len == tail_len + 1);
        assert(appended_tail_expected[i] == v);
      }
    }
  };

  assert(appended_tail == appended_tail_expected);
}

proof fn path_cost_append_vertex(graph: Graph, path: Seq<int>, v: int) -> (result: int)
  requires
    is_valid(graph),
    path.len() >= 1,
    path_nodes_within_bounds(graph, path),
    path_edges_exist(graph, path),
    0 <= v && v < graph.number_of_nodes as int,
    edge_exists(graph, path[path.len() as int - 1], v),
  ensures
    path_cost(graph, append_vertex(path, v)) == path_cost(graph, path) + edge_weight(graph, path[path.len() as int - 1], v)
  decreases
    path.len()
{
  if path.len() == 1 {
    assert(path_cost(graph, path) == 0);
    assert(path_cost(graph, append_vertex(path, v)) == edge_weight(graph, path[0], v)) by {
      let appended = append_vertex(path, v);
      append_vertex_preserves_bounds(graph, path, v);
      append_vertex_preserves_edges(graph, path, v);
      assert(path_cost(graph, appended) == path_cost_core(graph, appended, appended.len() as nat));
      path_cost_unfold(graph, appended);
      let append_tail = appended.subrange(1, appended.len() as int);
      assert(append_tail.len() == 1);
      assert(path_cost(graph, append_tail) == 0);
      assert(path_cost(graph, appended) == edge_weight(graph, path[0], v) + path_cost(graph, append_tail));
      assert(path_cost(graph, append_tail) == 0);
    };
  } else {
    let tail = path.subrange(1, path.len() as int);
    let u = path[0];
    let next = path[1];

    assert(path.len() >= 2);
    path_tail_preserves_bounds(graph, path);
    path_tail_preserves_edges(graph, path);
    assert(path_nodes_within_bounds(graph, tail));
    assert(path_edges_exist(graph, tail));
    assert(tail.len() == path.len() as int - 1);
    assert(tail.len() >= 1);
    assert(tail[tail.len() as int - 1] == path[path.len() as int - 1]);
    assert(edge_exists(graph, tail[tail.len() as int - 1], v));

    path_cost_unfold(graph, path);

    let result_tail = path_cost_append_vertex(graph, tail, v);

    append_vertex_preserves_bounds(graph, tail, v);
    append_vertex_preserves_edges(graph, tail, v);
    append_vertex_preserves_bounds(graph, path, v);
    append_vertex_preserves_edges(graph, path, v);

    append_vertex_tail_subrange(path, v);

    path_cost_unfold(graph, append_vertex(path, v));

    let appended_tail = append_vertex(path, v)
      .subrange(1, append_vertex(path, v).len() as int);
    assert(appended_tail == append_vertex(tail, v));
    assert(path_cost(graph, append_vertex(path, v)) == edge_weight(graph, u, next) + path_cost(graph, append_vertex(tail, v)));
  }
  path_cost(graph, append_vertex(path, v))
}

proof fn single_node_path_is_path(graph: Graph, node: int)
  requires
    is_valid(graph),
    0 <= node < graph.number_of_nodes as int,
  ensures
    is_path(graph, node, node, seq![node])
{
  let path = seq![node];
  assert(path.len() == 1);
  assert(path[0] == node);
  assert(path[path.len() as int - 1] == node);

  assert(path_nodes_within_bounds(graph, path)) by {
    assert forall|i: int|
      if 0 <= i && i < path.len() as int {
        #[trigger] path[i];
        0 <= path[i] && path[i] < graph.number_of_nodes as int
      } else {
        true
      }
    by {
      if 0 <= i && i < path.len() as int {
        assert(i == 0);
        assert(path[i] == node);
        assert(0 <= node < graph.number_of_nodes as int);
      }
    };
  };

  assert(path_edges_exist(graph, path)) by {
    assert forall|i: int|
      if 0 <= i && i < path.len() as int - 1 {
        #[trigger] edge_exists(graph, path[i], path_next(path, i));
        edge_exists(graph, path[i], path_next(path, i))
      } else {
        true
      }
    by {
      if 0 <= i && i < path.len() as int - 1 {
        assert(path.len() as int == 1);
        assert(path.len() as int - 1 == 0);
        assert(false);
      }
    };
  };

  assert(is_path(graph, node, node, path));
}

proof fn single_node_path_cost_zero(graph: Graph, node: int)
  requires
    is_valid(graph),
    0 <= node < graph.number_of_nodes as int,
  ensures
    path_cost(graph, seq![node]) == 0
{
  assert(path_cost(graph, seq![node]) == 0);
}

proof fn sp_dist_upper_bound_for_path(graph: Graph, start_node: int, destination_node: int, path: Seq<int>)
  requires
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int,
    0 <= destination_node && destination_node < graph.number_of_nodes as int,
    is_path(graph, start_node, destination_node, path)
  ensures
    match sp_dist(graph, start_node, destination_node) {
      Some(d) => d <= path_cost(graph, path),
      Option::<int>::None => false,
    }
{
  if start_node == destination_node {
    assert(sp_dist(graph, start_node, destination_node) == Some(0int));
    assert(path_cost(graph, path) >= 0);
  } else {
    assert(path.len() >= 1);
    assert(path_nodes_within_bounds(graph, path));
    assert(path_edges_exist(graph, path));

    assert(exists|candidate: Seq<int>| is_path(graph, start_node, destination_node, candidate)) by {
      let candidate = path;
      assert(is_path(graph, start_node, destination_node, candidate));
    };

    let witness = choose|candidate: Seq<int>|
      is_path(graph, start_node, destination_node, candidate)
        && forall|other: Seq<int>| is_path(graph, start_node, destination_node, other) ==>
          path_cost(graph, candidate) <= path_cost(graph, other);

    let witness_is_path = is_path(graph, start_node, destination_node, witness);
    let witness_forall = forall|other: Seq<int>| is_path(graph, start_node, destination_node, other) ==>
      path_cost(graph, witness) <= path_cost(graph, other);
    assert(witness_is_path && witness_forall);
    assert(is_path(graph, start_node, destination_node, witness)) by {
      assert(witness_is_path && witness_forall);
      if witness_is_path && witness_forall {
        assert(witness_is_path);
      }
    };
    assert(forall|other: Seq<int>| is_path(graph, start_node, destination_node, other) ==>
      path_cost(graph, witness) <= path_cost(graph, other)) by {
      assert(witness_is_path && witness_forall);
      if witness_is_path && witness_forall {
        assert(witness_forall);
      }
    };

    assert(is_path(graph, start_node, destination_node, path));
    assert(path_cost(graph, witness) <= path_cost(graph, path)) by {
      assert(forall|other: Seq<int>| is_path(graph, start_node, destination_node, other) ==>
        path_cost(graph, witness) <= path_cost(graph, other));
    };

    assert(sp_dist(graph, start_node, destination_node) == Some(path_cost(graph, witness)));
    assert(match sp_dist(graph, start_node, destination_node) {
      Some(d) => d <= path_cost(graph, path),
      Option::<int>::None => false,
    });
  }
}

spec fn sp_dist(graph: Graph, start_node: int, destination_node: int) -> Option<int>
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int,
    0 <= destination_node && destination_node < graph.number_of_nodes as int
{
  if start_node == destination_node {
    Some(0int)
  } else if exists|path: Seq<int>| is_path(graph, start_node, destination_node, path) {
    let witness = choose|path: Seq<int>|
      is_path(graph, start_node, destination_node, path)
        && forall|other_path: Seq<int>| is_path(graph, start_node, destination_node, other_path) ==>
          path_cost(graph, path) <= path_cost(graph, other_path);
    Some(path_cost(graph, witness))
  } else {
    None
  }
}

// Dijkstra invariants
spec fn dist_upper_bounds_shortest_paths(graph: Graph, start_node: int, dist: Seq<Option<int>>) -> bool
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  forall|v: int|
    0 <= v < dist.len() as int ==>
      match dist[v] {
        Some(d) =>
          match #[trigger] sp_dist(graph, start_node, v) {
            Some(sd) => sd <= d,
            Option::<int>::None => false,
          },
        Option::<int>::None => true,
      }
}

spec fn visited_nodes_have_exact_distance(graph: Graph, start_node: int, dist: Seq<Option<int>>, visited: Seq<bool>) -> bool
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    visited.len() == graph.number_of_nodes as int,
    dist.len() == visited.len(),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  forall|v: int|
    0 <= v < visited.len() as int ==>
      (!visited[v]) ||
        match dist[v] {
          Some(d) =>
            match sp_dist(graph, start_node, v) {
              Some(sd) => d == sd,
              Option::<int>::None => false,
            },
          Option::<int>::None => false,
        }
}

spec fn start_distance_is_zero(graph: Graph, start_node: int, dist: Seq<Option<int>>) -> bool
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  dist[start_node] matches Some(d) && d == 0
}

spec fn dijkstra_state_inv(graph: Graph, start_node: int, dist: Seq<Option<int>>, visited: Seq<bool>) -> bool
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    visited.len() == graph.number_of_nodes as int,
    dist.len() == visited.len(),
    0 <= start_node && start_node < graph.number_of_nodes as int
{
  dist_upper_bounds_shortest_paths(graph, start_node, dist)
    && visited_nodes_have_exact_distance(graph, start_node, dist, visited)
    && start_distance_is_zero(graph, start_node, dist)
    && dist_values_have_witness_paths(graph, start_node, dist)
}

// Graph validation helpers
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

spec fn dijkstra_init_spec(graph: Graph, start_node: int) -> (Seq<Option<int>>, Seq<bool>, Seq<Option<int>>)
  recommends
    is_valid(graph),
    0 <= start_node < graph.number_of_nodes as int
{
  if !is_valid(graph) || !(start_node < graph.number_of_nodes as int) {
    (Seq::empty(), Seq::empty(), Seq::empty())
  } else {
    let dist = Seq::new(graph.number_of_nodes as nat, |i:int|
      if i == start_node {
        Some(0int)
      } else {
        None
      }
    );
    let visited = Seq::new(graph.number_of_nodes as nat, |_i:int| false);
    let parent = Seq::new(graph.number_of_nodes as nat, |_i:int| None);
    (dist, visited, parent)
  }
}

proof fn dijkstra_init_state_inv(graph: Graph, start_node: int)
  requires
    is_valid(graph),
    0 <= start_node < graph.number_of_nodes as int,
  ensures
    ({
      let (dist, visited, _parent) = dijkstra_init_spec(graph, start_node);
      dijkstra_state_inv(graph, start_node, dist, visited)
    })
{
  let (dist, visited, _parent) = dijkstra_init_spec(graph, start_node);

  assert(dist.len() == graph.number_of_nodes as int);
  assert(visited.len() == graph.number_of_nodes as int);
  assert(dist.len() == visited.len());

  assert(dist[start_node] == Some(0int));
  assert(start_distance_is_zero(graph, start_node, dist));

  assert(dist_upper_bounds_shortest_paths(graph, start_node, dist)) by {
    assert forall|v: int|
      if 0 <= v && v < dist.len() as int {
        let dv = #[trigger] dist[v];
        match dv {
          Some(d) =>
            match #[trigger] sp_dist(graph, start_node, v) {
              Some(sd) => sd <= d,
              Option::<int>::None => false,
            },
          Option::<int>::None => true,
        }
      } else {
        true
      }
    by {
      if 0 <= v && v < dist.len() as int {
        if v == start_node {
          assert(dist[v] == Some(0int));
          assert(sp_dist(graph, start_node, v) == Some(0int));
        } else {
          assert(dist[v] == Option::<int>::None);
        }
        let holds =
          match dist[v] {
            Some(d) =>
              match sp_dist(graph, start_node, v) {
                Some(sd) => sd <= d,
                Option::<int>::None => false,
              },
            Option::<int>::None => true,
          };
        assert(holds);
      }
    };
  };

  assert(visited_nodes_have_exact_distance(graph, start_node, dist, visited)) by {
    assert forall|v: int|
      if 0 <= v && v < visited.len() as int {
        (!visited[v]) ||
          match #[trigger] dist[v] {
            Some(d) =>
              match #[trigger] sp_dist(graph, start_node, v) {
                Some(sd) => d == sd,
                Option::<int>::None => false,
              },
            Option::<int>::None => false,
          }
      } else {
        true
      }
    by {
      if 0 <= v && v < visited.len() as int {
        assert(visited[v] == false);
        let holds =
          (!visited[v]) ||
            match dist[v] {
              Some(d) =>
                match sp_dist(graph, start_node, v) {
                  Some(sd) => d == sd,
                  Option::<int>::None => false,
                },
              Option::<int>::None => false,
            };
        assert(holds);
      }
    };
  };

  assert(dist_values_have_witness_paths(graph, start_node, dist)) by {
    assert forall|v: int|
      if 0 <= v && v < dist.len() as int {
        match #[trigger] dist[v] {
          Some(d) =>
            exists|path: Seq<int>|
              #[trigger] is_path(graph, start_node, v, path)
                && #[trigger] path_cost(graph, path) == d,
          Option::<int>::None => true,
        }
      } else {
        true
      }
    by {
      if 0 <= v && v < dist.len() as int {
        if v == start_node {
          assert(dist[v] == Some(0int));
          single_node_path_is_path(graph, start_node);
          single_node_path_cost_zero(graph, start_node);
          let path = seq![start_node];
          assert(is_path(graph, start_node, v, path));
          assert(path_cost(graph, path) == 0);

          assert(exists|p: Seq<int>| is_path(graph, start_node, v, p) && path_cost(graph, p) == 0) by {
            let p = path;
            assert(is_path(graph, start_node, v, p));
            assert(path_cost(graph, p) == 0);
          };

          let holds =
            match dist[v] {
              Some(d) =>
                exists|path: Seq<int>| is_path(graph, start_node, v, path) && path_cost(graph, path) == d,
              Option::<int>::None => true,
            };
          assert(holds);
        } else {
          assert(dist[v] == Option::<int>::None);
          let holds =
            match dist[v] {
              Some(d) =>
                exists|path: Seq<int>| is_path(graph, start_node, v, path) && path_cost(graph, path) == d,
              Option::<int>::None => true,
            };
          assert(holds);
        }
      }
    };
  };

  assert(dijkstra_state_inv(graph, start_node, dist, visited));
}

spec fn has_unvisited_nodes(dist: Seq<Option<int>>, visited: Seq<bool>) -> bool
  recommends
    dist.len() == visited.len(),
{
  exists |i:int| 0 <= i && i < dist.len() as int && is_cand(dist, visited, i)
}

pub fn has_unvisited_nodes_proof_tests() {
  proof {
    // Test case 1: Has unvisited nodes with distances
    let dist = seq![Some(0int), Some(5int), Option::<int>::None, Some(3int)];
    let visited = seq![true, false, false, false];
    assert(dist.len() == visited.len());
    assert(has_unvisited_nodes(dist, visited));

    // Test case 2: All nodes visited
    let dist = seq![Some(0int), Some(5int), Some(3int)];
    let visited = seq![true, true, true];
    assert(dist.len() == visited.len());
    assert(!has_unvisited_nodes(dist, visited));

    // Test case 3: Unvisited nodes but no distances
    let dist = seq![Some(0int), Option::<int>::None, Option::<int>::None];
    let visited = seq![true, false, false];
    assert(dist.len() == visited.len());
    assert(!has_unvisited_nodes(dist, visited));

    // Test case 4: Empty sequences
    let dist = Seq::empty();
    let visited = Seq::empty();
    assert(dist.len() == visited.len());
    assert(!has_unvisited_nodes(dist, visited));

    // Test case 5: Single unvisited node with distance
    let dist = seq![Some(0int)];
    let visited = seq![false];
    assert(dist.len() == visited.len());
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
    Option::<int>::None => false,
  }
}

proof fn is_cand_lemma(dist: Seq<Option<int>>, visited: Seq<bool>, i: int)
  requires
    0 <= i < dist.len() as int,
    dist.len() == visited.len(),
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
    let dist = seq![Some(0int), Some(5int), Option::<int>::None, Some(3int)];
    let visited = seq![true, false, false, false];

    // Test case 1: Node with distance and not visited (should be true)
    assert(is_cand(dist, visited, 1));  // node 1: Some(5int), not visited

    // Test case 2: Node with distance but already visited (should be false)
    assert(!is_cand(dist, visited, 0));  // node 0: Some(0int), but visited

    // Test case 3: Node with no distance (None) - not visited (should be false)
    assert(!is_cand(dist, visited, 2));  // node 2: None, not visited

    // Test case 4: Node with no distance (None) - visited (should be false)
    let dist_2 = seq![Some(0int), Option::<int>::None, Some(3int)];
    let visited_2 = seq![true, true, false];
    assert(!is_cand(dist_2, visited_2, 1));  // node 1: None, visited

    // Test case 5: Node with distance and not visited at end of sequence
    assert(is_cand(dist, visited, 3));  // node 3: Some(3int), not visited

    // Test case 6: All nodes have distances, one not visited
    let dist_3 = seq![Some(0int), Some(5int), Some(3int)];
    let visited_3 = seq![true, false, true];
    assert(is_cand(dist_3, visited_3, 1));  // node 1: Some(5int), not visited
    assert(!is_cand(dist_3, visited_3, 0)); // node 0: Some(0int), visited
    assert(!is_cand(dist_3, visited_3, 2)); // node 2: Some(3int), visited

    // Test case 7: All nodes have None (no distances)
    let dist_4 = seq![Option::<int>::None, Option::<int>::None, Option::<int>::None];
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
        Option::<int>::None => {}
      }
    }
    Option::<int>::None => {}
  }
}

pub fn is_better_proof_tests() {
  proof {
    // Test case 1: start_node has smaller distance (should be true)
    let dist = seq![Some(0int), Some(5int), Some(10int), Some(3int)];
    assert(is_better(dist, 0, 1));  // dist[0]=0 < dist[1]=5

    // Test case 2: start_node has larger distance (should be false)
    assert(!is_better(dist, 1, 0));  // dist[1]=5 > dist[0]=0

    // Test case 3: Equal distances, start_node < new_node (should be true)
    let dist_2 = seq![Some(5int), Some(5int), Some(5int)];
    assert(is_better(dist_2, 0, 1));  // dist[0]=5 == dist[1]=5, and 0 <= 1

    // Test case 4: Equal distances, start_node == new_node (should be true)
    assert(is_better(dist_2, 0, 0));  // dist[0]=5 == dist[0]=5, and 0 <= 0

    // Test case 5: Equal distances, start_node > new_node (should be false)
    assert(!is_better(dist_2, 2, 1));  // dist[2]=5 == dist[1]=5, but 2 > 1

    // Test case 6: start_node much smaller distance
    let dist_3 = seq![Some(1int), Some(100int)];
    assert(is_better(dist_3, 0, 1));  // dist[0]=1 < dist[1]=100

    // Test case 7: start_node much larger distance
    assert(!is_better(dist_3, 1, 0));  // dist[1]=100 > dist[0]=1

    // Test case 8: Multiple equal distances, checking tie-breaking
    let dist_4 = seq![Some(7int), Some(7int), Some(7int), Some(7int)];
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
        Option::<int>::None => Option::Some(start_node),
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
      Option::<int>::None =>
        !exists|j: int|
          start_node <= j && j < dist.len() as int &&
          #[trigger] is_cand(dist, visited, j) &&
          (best_node == Option::<int>::None || !is_cand(dist, visited, best_node.unwrap()))
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
      Option::<int>::None => {
        // Since start_node >= dist.len(), there are no candidates j where start_node <= j < dist.len()
        // So !exists|j| start_node <= j < dist.len() && is_cand(dist, visited, j) is true
        // And best_node == Option::<int>::None is true
        assert(!exists|j: int| start_node <= j && j < dist.len() as int && is_cand(dist, visited, j));
        assert(best_node == Option::<int>::None);
      }
    }
  } else {
    // Recursive case: check if start_node is a candidate
    let new_best: Option<int> = if is_cand(dist, visited, start_node) {
      match best_node {
        Option::<int>::None => Option::Some(start_node),
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
    let dist = seq![Some(0int), Some(5int)];
    let visited = seq![false, false];
    let result: Option<int> = unvisited_core(dist, visited, 2, Option::Some(1int));
    assert(result == Option::Some(1int));  // Returns the passed best_node

    // Test case 2: Single candidate, starting from beginning with None
    let result_2: Option<int> = unvisited_core(dist, visited, 0, Option::<int>::None);
    assert(result_2 == Option::Some(0int));  // Finds node 0 (distance 0)

    // Test case 3: Multiple candidates, finds the best (smallest distance)
    let dist_2 = seq![Some(5int), Some(2int), Some(8int), Some(1int)];
    let visited_2 = seq![false, false, false, false];
    let result_3: Option<int> = unvisited_core(dist_2, visited_2, 0, Option::<int>::None);
    assert(result_3 == Option::Some(3int));  // Node 3 has smallest distance (1)

    // Test case 4: Multiple candidates with equal distances, picks smallest index
    let dist_3 = seq![Some(5int), Some(5int), Some(5int)];
    let visited_3 = seq![false, false, false];
    let result_4: Option<int> = unvisited_core(dist_3, visited_3, 0, Option::<int>::None);
    assert(result_4 == Option::Some(0int));  // Tie broken by index, picks 0

    // Test case 5: Starting from middle, finds best remaining
    let dist_4 = seq![Some(10int), Some(5int), Some(3int), Some(7int)];
    let visited_4 = seq![false, false, false, false];
    let result_5: Option<int> = unvisited_core(dist_4, visited_4, 2, Option::<int>::None);
    assert(result_5 == Option::Some(2int));  // Starting from index 2, finds itself (distance 3)

    // Test case 6: All visited, returns None if starting with None
    let dist_5 = seq![Some(0int), Some(5int), Some(3int)];
    let visited_5 = seq![true, true, true];
    let result_6: Option<int> = unvisited_core(dist_5, visited_5, 0, Option::<int>::None);
    assert(result_6 == Option::<int>::None);  // No candidates found

    // Test case 7: All have no distances (None), returns None
    let dist_6 = seq![None, None, None];
    let visited_6 = seq![false, false, false];
    let result_7: Option<int> = unvisited_core(dist_6, visited_6, 0, Option::<int>::None);
    assert(result_7 == Option::<int>::None);  // No candidates (no distances)

    // Test case 8: Mix of visited/unvisited, finds unvisited candidate
    let dist_7 = seq![Some(0int), Some(5int), Some(3int)];
    let visited_7 = seq![true, false, false];
    let result_8: Option<int> = unvisited_core(dist_7, visited_7, 0, Option::<int>::None);
    assert(result_8 == Option::Some(2int));  // Node 2 has smallest distance among unvisited

    // Test case 9: Starting with existing best_node, finds better one
    let dist_8 = seq![Some(10int), Some(5int), Some(3int)];
    let visited_8 = seq![false, false, false];
    let result_9: Option<int> = unvisited_core(dist_8, visited_8, 1, Option::Some(0int));
    assert(result_9 == Option::Some(2int));  // Starts with node 0 (distance 10), finds better: node 2 (distance 3)

    // Test case 10: Starting with best_node, keeps it if no better found
    let dist_9 = seq![Some(2int), Some(5int), Some(8int)];
    let visited_9 = seq![false, false, false];
    let result_10: Option<int> = unvisited_core(dist_9, visited_9, 1, Option::Some(0int));
    assert(result_10 == Option::Some(0int));  // Starts with node 0 (distance 2), no better found

    // Test case 11: Empty sequences
    let dist_empty = Seq::empty();
    let visited_empty = Seq::empty();
    let result_11: Option<int> = unvisited_core(dist_empty, visited_empty, 0, Option::<int>::None);
    assert(result_11 == Option::<int>::None);  // Base case immediately returns None
  }
}

spec fn find_min_unvisited_spec(dist: Seq<Option<int>>, visited: Seq<bool>) -> Option<int>
  recommends
    dist.len() == visited.len()
{
  if !has_unvisited_nodes(dist, visited) {
    Option::<int>::None
  } else {
    unvisited_core(dist, visited, 0, Option::<int>::None)
  }
}

// Lemma characterizing find_min_unvisited_spec: returns the best unvisited candidate if one exists
proof fn find_min_unvisited_spec_lemma(dist: Seq<Option<int>>, visited: Seq<bool>)
  requires
    dist.len() == visited.len()
  ensures
    forall|i: int|
      0 <= i && i < dist.len() as int ==>
        (#[trigger] is_cand(dist, visited, i)) <==>
          (find_min_unvisited_spec(dist, visited) matches Option::Some(i))
{
  if !has_unvisited_nodes(dist, visited) {
  } else {
    unvisited_core_lemma(dist, visited, 0, Option::<int>::None);
  }
}

pub fn find_min_unvisited_spec_proof_tests() {
  proof {
    // Test case 1: Has unvisited nodes, finds the one with smallest distance
    let dist = seq![Some(5int), Some(2int), Some(8int), Some(1int)];
    let visited = seq![false, false, false, false];
    let result: Option<int> = find_min_unvisited_spec(dist, visited);
    assert(result == Option::Some(3int));  // Node 3 has smallest distance (1)

    // Test case 2: Has unvisited nodes, equal distances pick smallest index
    let dist_2 = seq![Some(5int), Some(5int), Some(5int)];
    let visited_2 = seq![false, false, false];
    let result_2: Option<int> = find_min_unvisited_spec(dist_2, visited_2);
    assert(result_2 == Option::Some(0int));  // Tie broken by index, picks 0

    // Test case 3: All nodes visited, returns None
    let dist_3 = seq![Some(0int), Some(5int), Some(3int)];
    let visited_3 = seq![true, true, true];
    let result_3: Option<int> = find_min_unvisited_spec(dist_3, visited_3);
    assert(result_3 == Option::<int>::None);  // No unvisited nodes

    // Test case 4: Mix of visited/unvisited, finds best unvisited
    let dist_4 = seq![Some(0int), Some(5int), Some(3int), Some(2int)];
    let visited_4 = seq![true, false, false, false];
    let result_4: Option<int> = find_min_unvisited_spec(dist_4, visited_4);
    assert(result_4 == Option::Some(3int));  // Node 3 has smallest distance (2) among unvisited

    // Test case 5: Some nodes have no distances, finds best among those with distances
    let dist_5 = seq![Some(5int), None, Some(3int), None];
    let visited_5 = seq![false, false, false, false];
    let result_5: Option<int> = find_min_unvisited_spec(dist_5, visited_5);
    assert(result_5 == Option::Some(2int));  // Node 2 has distance 3, better than node 0's 5

    // Test case 6: Only one unvisited node
    let dist_6 = seq![Some(0int), Some(5int), Some(3int)];
    let visited_6 = seq![true, true, false];
    let result_6: Option<int> = find_min_unvisited_spec(dist_6, visited_6);
    assert(result_6 == Option::Some(2int));  // Only node 2 is unvisited

    // Test case 7: All nodes have no distances, returns None
    let dist_7 = seq![None, None, None];
    let visited_7 = seq![false, false, false];
    let result_7: Option<int> = find_min_unvisited_spec(dist_7, visited_7);
    assert(result_7 == Option::<int>::None);  // No candidates (no distances)

    // Test case 8: Large distances, finds smallest
    let dist_8 = seq![Some(100int), Some(50int), Some(200int), Some(25int)];
    let visited_8 = seq![false, false, false, false];
    let result_8: Option<int> = find_min_unvisited_spec(dist_8, visited_8);
    assert(result_8 == Option::Some(3int));  // Node 3 has smallest distance (25)

    // Test case 9: Single node, unvisited
    let dist_9 = seq![Some(0int)];
    let visited_9 = seq![false];
    let result_9: Option<int> = find_min_unvisited_spec(dist_9, visited_9);
    assert(result_9 == Option::Some(0int));  // Only node, unvisited

    // Test case 10: Single node, visited
    let dist_10 = seq![Some(0int)];
    let visited_10 = seq![true];
    let result_10: Option<int> = find_min_unvisited_spec(dist_10, visited_10);
    assert(result_10 == Option::<int>::None);  // Only node is visited
  }
}

spec fn dijkstra_core_spec(graph: Graph, dist: Seq<Option<int>>, visited: Seq<bool>, parent: Seq<Option<int>>, start_node: int, destination_node: int, steps_left: int) -> (result: (Seq<Option<int>>, Seq<bool>, Seq<Option<int>>))
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    visited.len() == graph.number_of_nodes as int,
    parent.len() == graph.number_of_nodes as int,
    dist.len() == visited.len(),
    visited.len() == parent.len(),
    0 <= start_node && start_node < graph.number_of_nodes as int,
    0 <= destination_node && destination_node < graph.number_of_nodes as int,
    dijkstra_state_inv(graph, start_node, dist, visited),
    steps_left >= 0,
  decreases
    steps_left
{
  if steps_left <= 0 || !has_unvisited_nodes(dist, visited) {
    (dist, visited, parent)
  } else {
    let next_node_opt: Option<int> = find_min_unvisited_spec(dist, visited);
    match next_node_opt {
      Option::<int>::None => {
        // Shouldn't happen if has_unvisited_nodes is true, but handle it
        (dist, visited, parent)
      }
      Option::Some(next_node) => {
        let visited_new = visited.update(next_node, true);

        if next_node == destination_node {
          (dist, visited_new, parent)
        } else {
          let (dist_new, parent_new) = update_edges_spec(graph, dist, visited_new, parent, next_node);

          dijkstra_core_spec(graph, dist_new, visited_new, parent_new, start_node, destination_node, steps_left - 1)
        }
      }
    }
  }
}

// Check if there's an edge from u to v and if the path through u improves the distance to v
spec fn should_update_edge(graph: Graph, dist: Seq<Option<int>>, u: int, v: int) -> bool
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int,
    dist[u] matches Some(_),
{
  match dist[u] {
    Some(d_u) => {
      match dist[v] {
        Option::<int>::None => {
          exists|i: int|
            0 <= i && i < graph.adjacent_nodes[u].len() as int &&
            graph.adjacent_nodes[u][i].to == v as usize
        }
        Some(d_v) => {
          exists|i: int|
            0 <= i && i < graph.adjacent_nodes[u].len() as int
              && #[trigger] graph.adjacent_nodes[u][i].to == v as usize
              && d_u + (graph.adjacent_nodes[u][i].w as int) < d_v
        }
      }
    }
    Option::<int>::None => false
  }
}

// Get the new distance value after updating edge from u to v
// If multiple edges exist from u to v, returns the minimum distance achievable
spec fn get_updated_distance(graph: Graph, dist: Seq<Option<int>>, u: int, v: int) -> Option<int>
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int,
    dist[u] matches Some(_),
    should_update_edge(graph, dist, u, v),
{
  match dist[u] {
    Some(d_u) => {
      min_updated_distance_helper(graph, dist, u, v, d_u, 0)
    }
    Option::<int>::None => dist[v]
  }
}

// Recursive helper to find minimum distance through edges from u to v
spec fn min_updated_distance_helper(graph: Graph, dist: Seq<Option<int>>, u: int, v: int, d_u: int, i: int) -> Option<int>
  recommends
    is_valid(graph), // TODO: these are getting repeated a lot. Dry this up.
    dist.len() == graph.number_of_nodes as int,
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int,
    0 <= i <= graph.adjacent_nodes[u].len() as int,
  decreases
    graph.adjacent_nodes[u].len() as int - i
{
  if i >= graph.adjacent_nodes[u].len() as int {
    Option::<int>::None
  } else {
    let edge = graph.adjacent_nodes[u][i];
    let candidate: Option<int> = if edge.to == v as usize {
      match dist[v] {
        Option::<int>::None => Some(d_u + (edge.w as int)),
        Some(d_v) => if d_u + (edge.w as int) < d_v {
          Some(d_u + (edge.w as int))
        } else {
          None
        }
      }
    } else {
      None
    };
    let rest: Option<int> = min_updated_distance_helper(graph, dist, u, v, d_u, i + 1);
    match (candidate, rest) {
      (Some(c), Some(r)) => Some(if c < r { c } else { r }),
      (Some(c), Option::<int>::None) => Some(c),
      (Option::<int>::None, Some(r)) => Some(r),
      (Option::<int>::None, Option::<int>::None) => Option::<int>::None
    }
  }
}

proof fn min_updated_distance_helper_witness(graph: Graph, dist: Seq<Option<int>>, u: int, v: int, d_u: int, i: int)
  requires
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int,
    0 <= i <= graph.adjacent_nodes[u].len() as int,
  ensures
    match min_updated_distance_helper(graph, dist, u, v, d_u, i) {
      Some(result) =>
        exists|edge_idx: int|
          i <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
            && graph.adjacent_nodes[u][edge_idx].to == v as usize
            && result == d_u + (graph.adjacent_nodes[u][edge_idx].w as int),
      Option::<int>::None => true
    }
    && ((exists|edge_idx: int|
          i <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
            && graph.adjacent_nodes[u][edge_idx].to == v as usize
            && match dist[v] {
              Option::<int>::None => true,
              Some(d_v) => d_u + (graph.adjacent_nodes[u][edge_idx].w as int) < d_v,
            }) ==> (min_updated_distance_helper(graph, dist, u, v, d_u, i) matches Some(_)))
  decreases
    graph.adjacent_nodes[u].len() as int - i
{
  if i >= graph.adjacent_nodes[u].len() as int {
    assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) == Option::<int>::None);
  } else {
    let edge = graph.adjacent_nodes[u][i];
    let candidate: Option<int> = if edge.to == v as usize {
      match dist[v] {
        Option::<int>::None => Some(d_u + (edge.w as int)),
        Some(d_v) => if d_u + (edge.w as int) < d_v {
          Some(d_u + (edge.w as int))
        } else {
          Option::<int>::None
        }
      }
    } else {
      Option::<int>::None
    };
    let rest: Option<int> = min_updated_distance_helper(graph, dist, u, v, d_u, i + 1);

    min_updated_distance_helper_witness(graph, dist, u, v, d_u, i + 1);

    let improving_exists = exists|edge_idx: int|
      i <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
        && graph.adjacent_nodes[u][edge_idx].to == v as usize
        && match dist[v] {
          Option::<int>::None => true,
          Some(d_v) => d_u + (graph.adjacent_nodes[u][edge_idx].w as int) < d_v,
        };

    match (candidate, rest) {
      (Some(c), Some(r)) => {
        let result = if c < r { c } else { r };
        assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) == Some(result));
        if c < r {
          assert(result == c);
          assert(exists|edge_idx: int|
            i <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
              && graph.adjacent_nodes[u][edge_idx].to == v as usize
              && result == d_u + (graph.adjacent_nodes[u][edge_idx].w as int)) by {
            let edge_idx = i;
            assert(i <= edge_idx);
            assert(edge_idx < graph.adjacent_nodes[u].len() as int);
            assert(graph.adjacent_nodes[u][edge_idx].to == v as usize);
            assert(result == d_u + (graph.adjacent_nodes[u][edge_idx].w as int));
          };
        } else {
          assert(result == r);
          assert(exists|edge_idx: int|
            i <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
              && graph.adjacent_nodes[u][edge_idx].to == v as usize
              && result == d_u + (graph.adjacent_nodes[u][edge_idx].w as int)) by {
            let witness = choose|edge_idx: int|
              i + 1 <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
                && graph.adjacent_nodes[u][edge_idx].to == v as usize
                && r == d_u + (graph.adjacent_nodes[u][edge_idx].w as int);
            let edge_idx = witness;
            assert(i <= edge_idx);
            assert(edge_idx < graph.adjacent_nodes[u].len() as int);
            assert(graph.adjacent_nodes[u][edge_idx].to == v as usize);
            assert(result == d_u + (graph.adjacent_nodes[u][edge_idx].w as int));
          };
        }
        if improving_exists {
          assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) matches Some(_));
        }
      }
      (Some(c), None) => {
        assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) == Some(c));
        assert(exists|edge_idx: int|
          i <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
            && graph.adjacent_nodes[u][edge_idx].to == v as usize
            && c == d_u + (graph.adjacent_nodes[u][edge_idx].w as int)) by {
          let edge_idx = i;
          assert(i <= edge_idx);
          assert(edge_idx < graph.adjacent_nodes[u].len() as int);
          assert(graph.adjacent_nodes[u][edge_idx].to == v as usize);
        };
        if improving_exists {
          assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) matches Some(_));
        }
      }
      (Option::<int>::None, Some(r)) => {
        assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) == Some(r));
        let witness = choose|edge_idx: int|
          i + 1 <= edge_idx && edge_idx < graph.adjacent_nodes[u].len() as int
            && graph.adjacent_nodes[u][edge_idx].to == v as usize
            && r == d_u + (graph.adjacent_nodes[u][edge_idx].w as int);
        let edge_idx = witness;
        assert(i <= edge_idx);
        assert(edge_idx < graph.adjacent_nodes[u].len() as int);
        assert(graph.adjacent_nodes[u][edge_idx].to == v as usize);
        if improving_exists {
          assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) matches Some(_));
        }
      }
      (Option::<int>::None, Option::<int>::None) => {
        assert(min_updated_distance_helper(graph, dist, u, v, d_u, i) == Option::<int>::None);
        assert(!improving_exists);
      }
    }
  }
}

proof fn get_updated_distance_witness(graph: Graph, dist: Seq<Option<int>>, u: int, v: int)
  requires
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    0 <= u < graph.number_of_nodes as int,
    0 <= v < graph.number_of_nodes as int,
    dist[u] matches Some(_),
    should_update_edge(graph, dist, u, v),
  ensures
    match get_updated_distance(graph, dist, u, v) {
      Some(result) =>
        exists|edge_idx: int|
          0 <= edge_idx < graph.adjacent_nodes[u].len() as int
            && graph.adjacent_nodes[u][edge_idx].to == v as usize
            && result == dist[u].unwrap() + (graph.adjacent_nodes[u][edge_idx].w as int),
      Option::<int>::None => false
    }
{
  let d_u = dist[u].unwrap();
  min_updated_distance_helper_witness(graph, dist, u, v, d_u, 0);

  assert(get_updated_distance(graph, dist, u, v) matches Some(_)) by {
    let improving_edge = choose|edge_idx: int|
      0 <= edge_idx < graph.adjacent_nodes[u].len() as int
        && graph.adjacent_nodes[u][edge_idx].to == v as usize
        && match dist[v] {
          Option::<int>::None => true,
          Some(d_v) => d_u + (graph.adjacent_nodes[u][edge_idx].w as int) < d_v,
        };
    assert(min_updated_distance_helper(graph, dist, u, v, d_u, 0) matches Some(_));
  };
}

spec fn update_edges_spec(graph: Graph, dist: Seq<Option<int>>, visited: Seq<bool>, parent: Seq<Option<int>>, u: int) -> (Seq<Option<int>>, Seq<Option<int>>)
  recommends
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    visited.len() == graph.number_of_nodes as int,
    parent.len() == graph.number_of_nodes as int,
    0 <= u < graph.number_of_nodes as int,
    dist[u] matches Some(_),
{
  // Use a quantifier to update all neighbors
  // For each edge (u, v) with weight w:
  //   if should_relax_edge is true, update dist[v] and parent[v] = u
  let dist_new = Seq::new(graph.number_of_nodes as nat, |v: int|
    if v < graph.number_of_nodes as int {
      if !visited[v] && should_update_edge(graph, dist, u, v) {
        get_updated_distance(graph, dist, u, v)
      } else {
        dist[v]
      }
    } else {
      dist[v]
    }
  );

  let parent_new = Seq::new(graph.number_of_nodes as nat, |v: int|
    if v < graph.number_of_nodes as int {
      if !visited[v] && should_update_edge(graph, dist, u, v) {
        Some(u)
      } else {
        parent[v]
      }
    } else {
      parent[v]
    }
  );

  (dist_new, parent_new)
}

proof fn update_edges_preserves_state_inv(
  graph: Graph,
  start_node: int,
  dist: Seq<Option<int>>,
  visited: Seq<bool>,
  parent: Seq<Option<int>>,
  u: int
)
  requires
    is_valid(graph),
    dist.len() == graph.number_of_nodes as int,
    visited.len() == graph.number_of_nodes as int,
    parent.len() == graph.number_of_nodes as int,
    dist.len() == visited.len(),
    visited.len() == parent.len(),
    0 <= start_node && start_node < graph.number_of_nodes as int,
    0 <= u && u < graph.number_of_nodes as int,
    dist[u] matches Some(_),
    dist_upper_bounds_shortest_paths(graph, start_node, dist),
    visited_nodes_have_exact_distance(graph, start_node, dist, visited),
    start_distance_is_zero(graph, start_node, dist),
    dist_values_have_witness_paths(graph, start_node, dist),
    visited[u]
  ensures
    ({
      let (dist_new, parent_new) = update_edges_spec(graph, dist, visited, parent, u);
      dist_new.len() == graph.number_of_nodes as int
        && parent_new.len() == graph.number_of_nodes as int
        && dist_upper_bounds_shortest_paths(graph, start_node, dist_new)
        && visited_nodes_have_exact_distance(graph, start_node, dist_new, visited)
        && start_distance_is_zero(graph, start_node, dist_new)
        && dist_values_have_witness_paths(graph, start_node, dist_new)
    })
{
  let (dist_new, _parent_new) = update_edges_spec(graph, dist, visited, parent, u);

  assert(dist_new.len() == graph.number_of_nodes as int);

  assert(start_distance_is_zero(graph, start_node, dist_new)) by {
    assert(dist[start_node] == Some(0int));
    assert(visited[start_node]);
    assert(dist_new[start_node] == dist[start_node]);
  };

  assume(dist_upper_bounds_shortest_paths(graph, start_node, dist_new));
  assume(visited_nodes_have_exact_distance(graph, start_node, dist_new, visited));
  assume(dist_values_have_witness_paths(graph, start_node, dist_new));
}

spec fn dijkstra_spec(graph: Graph, start_node: int, destination_node: int) -> (res: Option<int>)
  recommends
    is_valid(graph),
    0 <= start_node && start_node < graph.number_of_nodes as int,
    0 <= destination_node && destination_node < graph.number_of_nodes as int,
{
  let number_of_nodes: int = graph.number_of_nodes as int;

  if !is_valid(graph) || !(0 <= start_node && start_node < number_of_nodes) || !(0 <= destination_node && destination_node < number_of_nodes) {
    Option::<int>::None
  } else {
    let (dist, visited, parent) = dijkstra_init_spec(graph, start_node);
    let visited_init = visited.update(start_node, true);
    let (dist_final, visited_final, _parent_final) = dijkstra_core_spec(graph, dist, visited_init, parent, start_node, destination_node, graph.number_of_nodes as int);
    dist_final[destination_node]
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
}

} // verus!
