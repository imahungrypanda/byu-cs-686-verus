# Homework 6

Write a specification for Dijkstra's shortest path on a directed graph. Prove that the specification returns a path of shortest length. Implement Dijkstra's and prove that it refines the specification.

This problems requires a `struct` for the graph with an appropriate interface. That interface should have a `shortest_path` function that takes two nodes and returns the cost of the shortest path between the two nodes with the actual path. If the two nodes are not connected, or the nodes are not part of the graph, then it should return `None`.
