"""The tree estimator and its proposed extremal configurations."""

from __future__ import annotations

from .trees import Configuration, Tree, distances


def leaf_count(tree: Tree, root: int) -> int:
    """Count degree-one vertices other than ``root``."""
    return sum(vertex != root and len(tree[vertex]) == 1 for vertex in range(len(tree)))


def sigma(tree: Tree, root: int) -> int:
    """Return the paper's sigma_T(root), including its final +1."""
    distance = distances(tree, root)
    return 1 + sum(
        len(tree[vertex]) * 2 ** distance[vertex]
        for vertex in range(len(tree))
        if vertex == root or len(tree[vertex]) > 1
    )


def root_estimate(tree: Tree, root: int) -> int:
    return sigma(tree, root) + leaf_count(tree, root)


def estimate(tree: Tree) -> int:
    return max(root_estimate(tree, root) for root in range(len(tree)))


def extremal_configuration(tree: Tree, root: int) -> Configuration:
    """Place sigma(root)-1 at root and one at every other leaf."""
    result = [0] * len(tree)
    result[root] = sigma(tree, root) - 1
    for vertex in range(len(tree)):
        if vertex != root and len(tree[vertex]) == 1:
            result[vertex] = 1
    return tuple(result)


def obstruction_heights(tree: Tree, root: int) -> tuple[int | None, ...]:
    """Return the recursively defined ``h_v`` values away from ``root``.

    The root entry is ``None``.  Every other entry is one for a leaf and
    ``3 + 2 * sum(child heights)`` otherwise.
    """
    result: list[int | None] = [None] * len(tree)

    def visit(vertex: int, parent: int) -> int:
        children = [u for u in tree[vertex] if u != parent]
        if not children:
            value = 1
        else:
            value = 3 + 2 * sum(visit(child, vertex) for child in children)
        result[vertex] = value
        return value

    for child in tree[root]:
        visit(child, root)
    return tuple(result)
