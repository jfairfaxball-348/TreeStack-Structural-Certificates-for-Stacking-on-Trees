"""Structural branch-message computation for configured trees.

``None`` is the empty-branch marker.  It is deliberately distinct from the
integer message zero.
"""

from __future__ import annotations

from functools import lru_cache
from typing import Optional

from .trees import Configuration, Tree, validate_configuration

Message = Optional[int]
EMPTY: Message = None


def transfer(value: int) -> int:
    """The conjectured one-edge transfer map F."""
    if value <= 1:
        return 2 * value - 3
    if value == 2:
        return 1
    if value == 3:
        return 0
    if value % 2 == 0:
        return value // 2
    return (value - 3) // 2


def directed_messages(
    tree: Tree, configuration: Configuration
) -> dict[tuple[int, int], Message]:
    """Compute every oriented-edge branch message independently of a root."""
    state = validate_configuration(tree, configuration)

    @lru_cache(maxsize=None)
    def message(vertex: int, parent: int) -> Message:
        children = [u for u in tree[vertex] if u != parent]
        child_messages = [message(u, vertex) for u in children]
        if state[vertex] == 0 and all(item is EMPTY for item in child_messages):
            return EMPTY
        effective = state[vertex] + sum(
            item for item in child_messages if item is not EMPTY
        )
        return transfer(effective)

    return {
        (vertex, parent): message(vertex, parent)
        for vertex in range(len(tree))
        for parent in tree[vertex]
    }


def scores(tree: Tree, configuration: Configuration) -> tuple[int, ...]:
    """Return the structural score at every prospective stacking vertex."""
    state = validate_configuration(tree, configuration)
    messages = directed_messages(tree, state)
    return tuple(
        state[root]
        + sum(
            messages[(u, root)]
            for u in tree[root]
            if messages[(u, root)] is not EMPTY
        )
        for root in range(len(tree))
    )


def structurally_stackable_at(
    tree: Tree, configuration: Configuration, root: int
) -> bool:
    """Return the prediction ``S_root(C) > 0``."""
    return scores(tree, configuration)[root] > 0


def structurally_stackable(tree: Tree, configuration: Configuration) -> bool:
    """Return whether any structural root score is positive."""
    return any(score > 0 for score in scores(tree, configuration))

