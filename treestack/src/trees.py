"""Small immutable helpers for finite simple trees.

The computational core uses tuples of neighbour tuples so that it is not tied
to NetworkX.  NetworkX is used only by census and test-data generation code.
"""

from __future__ import annotations

from collections import deque
from typing import Iterable, Sequence, Tuple

Tree = Tuple[Tuple[int, ...], ...]
Configuration = Tuple[int, ...]


def make_tree(order: int, edges: Iterable[tuple[int, int]]) -> Tree:
    """Build and validate a tree on vertices ``range(order)``."""
    if order < 1:
        raise ValueError("a tree must have at least one vertex")
    neighbours = [set() for _ in range(order)]
    edge_count = 0
    for u, v in edges:
        if not (0 <= u < order and 0 <= v < order) or u == v:
            raise ValueError("invalid tree edge")
        if v in neighbours[u]:
            raise ValueError("duplicate edge")
        neighbours[u].add(v)
        neighbours[v].add(u)
        edge_count += 1
    if edge_count != order - 1:
        raise ValueError("a tree on n vertices must have n-1 edges")
    seen = {0}
    queue = deque([0])
    while queue:
        u = queue.popleft()
        for v in neighbours[u]:
            if v not in seen:
                seen.add(v)
                queue.append(v)
    if len(seen) != order:
        raise ValueError("tree is disconnected")
    return tuple(tuple(sorted(row)) for row in neighbours)


def validate_configuration(tree: Tree, configuration: Sequence[int]) -> Configuration:
    """Return a tuple after checking length and nonnegative integrality."""
    if len(configuration) != len(tree):
        raise ValueError("configuration length does not match the tree")
    if any(not isinstance(value, int) or value < 0 for value in configuration):
        raise ValueError("configuration entries must be nonnegative integers")
    return tuple(configuration)


def distances(tree: Tree, root: int) -> tuple[int, ...]:
    """Return all distances from ``root``."""
    result = [-1] * len(tree)
    result[root] = 0
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for v in tree[u]:
            if result[v] < 0:
                result[v] = result[u] + 1
                queue.append(v)
    return tuple(result)

