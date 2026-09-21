"""Exact forward reachability using only the legal pebbling rule.

This module intentionally knows nothing about branch messages.  It is the
small-instance oracle against which the structural solver is tested.
"""

from __future__ import annotations

from functools import lru_cache
from typing import Callable, Iterator

from .trees import Configuration, Tree, validate_configuration


def legal_children(tree: Tree, configuration: Configuration) -> Iterator[Configuration]:
    """Yield configurations one legal pebbling move away."""
    for source, value in enumerate(configuration):
        if value < 2:
            continue
        for target in tree[source]:
            child = list(configuration)
            child[source] -= 2
            child[target] += 1
            yield tuple(child)


def target_oracle(tree: Tree, root: int) -> Callable[[Configuration], bool]:
    """Create a memoized exact predicate for stackability at ``root``."""
    if not 0 <= root < len(tree):
        raise ValueError("root is not a vertex")

    @lru_cache(maxsize=None)
    def can_stack(state: Configuration) -> bool:
        if state[root] > 0 and all(
            value == 0 for vertex, value in enumerate(state) if vertex != root
        ):
            return True
        return any(can_stack(child) for child in legal_children(tree, state))

    def checked(configuration: Configuration) -> bool:
        return can_stack(validate_configuration(tree, configuration))

    return checked


def maximum_at_target_oracle(tree: Tree, root: int) -> Callable[[Configuration], int]:
    """Create an exact oracle for the largest reachable stack at ``root``.

    A return value of zero means that no positive configuration supported only
    at the target is reachable.  This stronger oracle tests the proposed
    ``q + d`` branch invariant, not only its positivity threshold.
    """
    if not 0 <= root < len(tree):
        raise ValueError("root is not a vertex")

    @lru_cache(maxsize=None)
    def maximum(state: Configuration) -> int:
        best = state[root] if all(
            value == 0 for vertex, value in enumerate(state) if vertex != root
        ) else 0
        return max((best, *(maximum(child) for child in legal_children(tree, state))))

    def checked(configuration: Configuration) -> int:
        return maximum(validate_configuration(tree, configuration))

    return checked


def stackable_at(tree: Tree, configuration: Configuration, root: int) -> bool:
    """Decide exact stackability at a prescribed vertex."""
    return target_oracle(tree, root)(configuration)


def stackable(tree: Tree, configuration: Configuration) -> bool:
    """Decide exact stackability at some vertex."""
    state = validate_configuration(tree, configuration)
    return any(target_oracle(tree, root)(state) for root in range(len(tree)))
