"""Independent theorem-level falsification checks.

This file deliberately does not import TreeStack's message, reachability,
estimator, or certificate implementations.  It recomputes the estimator from
the paper's formula and explores legal pebbling moves directly.
"""

from __future__ import annotations

from functools import lru_cache

import networkx as nx


def _configurations(order: int, total: int):
    if order == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for suffix in _configurations(order - 1, total - first):
            yield (first,) + suffix


def _adjacency(graph: nx.Graph) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(sorted(graph.neighbors(v))) for v in range(graph.number_of_nodes())
    )


def _distances(tree: tuple[tuple[int, ...], ...], root: int) -> tuple[int, ...]:
    result = [-1] * len(tree)
    result[root] = 0
    queue = [root]
    for u in queue:
        for v in tree[u]:
            if result[v] < 0:
                result[v] = result[u] + 1
                queue.append(v)
    return tuple(result)


def _estimate(tree: tuple[tuple[int, ...], ...]) -> int:
    values = []
    for root in range(len(tree)):
        distance = _distances(tree, root)
        sigma = 1 + sum(
            len(tree[v]) * 2 ** distance[v]
            for v in range(len(tree))
            if v == root or len(tree[v]) > 1
        )
        leaves = sum(v != root and len(tree[v]) == 1 for v in range(len(tree)))
        values.append(sigma + leaves)
    return max(values)


def _exact_stackability_solver(tree: tuple[tuple[int, ...], ...]):
    @lru_cache(maxsize=None)
    def stackable(state: tuple[int, ...]) -> bool:
        if sum(value > 0 for value in state) == 1:
            return True
        for source, value in enumerate(state):
            if value < 2:
                continue
            for target in tree[source]:
                child = list(state)
                child[source] -= 2
                child[target] += 1
                if stackable(tuple(child)):
                    return True
        return False

    return stackable


def test_estimator_threshold_independently_through_order_five() -> None:
    """Attack the headline formula without using structural messages/certificates."""
    for order in range(2, 6):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree = _adjacency(graph)
            estimator = _estimate(tree)
            stackable = _exact_stackability_solver(tree)

            assert any(
                not stackable(configuration)
                for configuration in _configurations(order, estimator - 1)
            )
            assert all(
                stackable(configuration)
                for configuration in _configurations(order, estimator)
            )
