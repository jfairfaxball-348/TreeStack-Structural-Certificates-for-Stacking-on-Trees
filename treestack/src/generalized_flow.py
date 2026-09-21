"""Exact zero-score generalized-flow certificates on trees.

This module implements the finite arithmetic used in the zero-score theorem.
It deliberately starts from genuine branch messages, so an empty branch is
never silently identified with the integer message zero.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Iterable, Sequence

from .estimator import estimate
from .messages import EMPTY, directed_messages, scores, transfer
from .trees import Configuration, Tree, distances, validate_configuration


@dataclass(frozen=True)
class EdgeState:
    """One genuine zero-score edge state.

    ``kind`` is ``"neutral"`` or ``"oriented"``.  On an oriented edge the
    positive message is sent from ``tail`` to ``head`` and has value
    ``parameter``; the reverse message is ``-2*parameter-3``.
    """

    u: int
    v: int
    kind: str
    tail: int | None = None
    head: int | None = None
    parameter: int | None = None


@dataclass(frozen=True)
class ZeroScoreCertificate:
    """Numerical chain certifying the zero-score estimator bound."""

    mass: int
    heights: tuple[int, ...]
    weighted_mass: int
    exact_edge_expansion: int
    relaxed_edge_expansion: int
    degree_height_potential: int
    leaf_term: int
    internal_height_potential: int
    consolidated_root: int
    consolidated_internal_potential: int
    maximum_root_internal_potential: int
    estimator_minus_one: int


def classify_message_pair(u: int, v: int, a: int, b: int) -> EdgeState:
    """Classify integer solutions of ``a=F(-b), b=F(-a)``.

    The arguments are ``a=d_{u->v}`` and ``b=d_{v->u}``.
    """
    if a != transfer(-b) or b != transfer(-a):
        raise ValueError("message pair does not satisfy the zero-score equations")
    if a == -1 and b == -1:
        return EdgeState(u=u, v=v, kind="neutral")
    if a >= 0 and b == -2 * a - 3:
        return EdgeState(
            u=u, v=v, kind="oriented", tail=u, head=v, parameter=a
        )
    if b >= 0 and a == -2 * b - 3:
        return EdgeState(
            u=u, v=v, kind="oriented", tail=v, head=u, parameter=b
        )
    raise AssertionError("unclassified integer solution of the edge equations")


def zero_score_edge_states(
    tree: Tree, configuration: Configuration
) -> tuple[EdgeState, ...]:
    """Return the exact edge-state model for a genuine zero-score configuration.

    The all-zero configuration is handled separately and returns no edge
    states.  For every nonzero zero-score configuration, every component of
    every edge deletion is nonempty; therefore all directed branch messages
    are integers and the edge-state classification applies literally.
    """
    state = validate_configuration(tree, configuration)
    if scores(tree, state) != (0,) * len(tree):
        raise ValueError("configuration does not have zero score at every vertex")
    if sum(state) == 0:
        return ()

    messages = directed_messages(tree, state)
    result: list[EdgeState] = []
    for u in range(len(tree)):
        for v in tree[u]:
            if u >= v:
                continue
            a = messages[(u, v)]
            b = messages[(v, u)]
            if a is EMPTY or b is EMPTY:
                raise AssertionError(
                    "a nonzero zero-score configuration cannot contain an empty "
                    "side of an edge"
                )
            result.append(classify_message_pair(u, v, a, b))
    return tuple(result)


def orientation_heights(order: int, states: Sequence[EdgeState]) -> tuple[int, ...]:
    """Longest directed-path length ending at each vertex."""
    incoming: list[list[int]] = [[] for _ in range(order)]
    for state in states:
        if state.kind == "oriented":
            assert state.tail is not None and state.head is not None
            incoming[state.head].append(state.tail)

    visiting: set[int] = set()

    @lru_cache(maxsize=None)
    def height(vertex: int) -> int:
        if vertex in visiting:
            raise ValueError("directed cycle in an edge-state orientation")
        visiting.add(vertex)
        try:
            return max((height(u) + 1 for u in incoming[vertex]), default=0)
        finally:
            visiting.remove(vertex)

    return tuple(height(v) for v in range(order))


def selected_height_partition(
    tree: Tree, states: Sequence[EdgeState], heights: Sequence[int]
) -> tuple[tuple[frozenset[int], int], ...]:
    """Partition into selected predecessor trees realizing the heights.

    For each positive-height vertex choose one incoming oriented edge that
    raises the height by exactly one.  Every resulting component has a unique
    height-zero root, and distance from that root equals the recorded height.
    """
    incoming: list[list[int]] = [[] for _ in range(len(tree))]
    for state in states:
        if state.kind == "oriented":
            assert state.tail is not None and state.head is not None
            incoming[state.head].append(state.tail)

    selected = [set() for _ in tree]
    for v, h in enumerate(heights):
        if h == 0:
            continue
        candidates = [u for u in incoming[v] if heights[u] + 1 == h]
        if not candidates:
            raise AssertionError("positive height has no realizing predecessor")
        u = min(candidates)
        selected[u].add(v)
        selected[v].add(u)

    unseen = set(range(len(tree)))
    parts: list[tuple[frozenset[int], int]] = []
    while unseen:
        start = min(unseen)
        stack = [start]
        component: set[int] = set()
        while stack:
            v = stack.pop()
            if v in component:
                continue
            component.add(v)
            unseen.discard(v)
            stack.extend(selected[v] - component)
        roots = [v for v in component if heights[v] == 0]
        if len(roots) != 1:
            raise AssertionError("selected height component must have one root")
        root = roots[0]
        distance = distances(tree, root)
        if any(distance[v] != heights[v] for v in component):
            raise AssertionError("selected predecessor distance does not equal height")
        parts.append((frozenset(component), root))
    return tuple(parts)


def _potential(
    tree: Tree, weights: Sequence[int], vertices: Iterable[int], root: int
) -> int:
    distance = distances(tree, root)
    return sum(weights[v] * 2 ** distance[v] for v in vertices)


def consolidate_connected_partition(
    tree: Tree,
    weights: Sequence[int],
    parts: Sequence[tuple[frozenset[int], int]],
) -> tuple[int, int]:
    """Consolidate a connected partition to one root without losing potential.

    This is the constructive form of the two-part merge lemma used in the
    proof.  It returns a root and the final whole-tree potential.
    """
    work = [(set(vertices), root) for vertices, root in parts]
    if not work:
        raise ValueError("partition must be nonempty")

    while len(work) > 1:
        owner = {}
        for index, (vertices, _) in enumerate(work):
            for v in vertices:
                owner[v] = index
        pair = None
        for u in range(len(tree)):
            for v in tree[u]:
                if owner[u] != owner[v]:
                    pair = (owner[u], owner[v])
                    break
            if pair is not None:
                break
        if pair is None:
            raise AssertionError("partition quotient is disconnected")
        i, j = pair
        if i > j:
            i, j = j, i
        vertices_i, root_i = work[i]
        vertices_j, root_j = work[j]
        old = _potential(tree, weights, vertices_i, root_i) + _potential(
            tree, weights, vertices_j, root_j
        )
        union = vertices_i | vertices_j
        potential_i = _potential(tree, weights, union, root_i)
        potential_j = _potential(tree, weights, union, root_j)
        if potential_i >= old:
            merged = (union, root_i)
        elif potential_j >= old:
            merged = (union, root_j)
        else:
            raise AssertionError("two-part exponential-potential merge failed")
        work.pop(j)
        work.pop(i)
        work.append(merged)

    vertices, root = work[0]
    if vertices != set(range(len(tree))):
        raise AssertionError("partition does not cover the tree")
    return root, _potential(tree, weights, vertices, root)


def zero_score_certificate(
    tree: Tree, configuration: Configuration
) -> ZeroScoreCertificate:
    """Build and verify the complete zero-score estimator certificate."""
    state = validate_configuration(tree, configuration)
    if scores(tree, state) != (0,) * len(tree):
        raise ValueError("configuration does not have zero score at every vertex")

    mass = sum(state)
    estimator_bound = estimate(tree) - 1
    if mass == 0:
        internal_weights = tuple(len(tree[v]) if len(tree[v]) > 1 else 0 for v in range(len(tree)))
        root_values = [
            _potential(tree, internal_weights, range(len(tree)), root)
            for root in range(len(tree))
        ]
        leaf_term = sum(len(tree[v]) == 1 for v in range(len(tree)))
        return ZeroScoreCertificate(
            mass=0,
            heights=(0,) * len(tree),
            weighted_mass=0,
            exact_edge_expansion=0,
            relaxed_edge_expansion=0,
            degree_height_potential=sum(len(row) for row in tree),
            leaf_term=leaf_term,
            internal_height_potential=sum(internal_weights),
            consolidated_root=max(range(len(tree)), key=root_values.__getitem__),
            consolidated_internal_potential=max(root_values),
            maximum_root_internal_potential=max(root_values),
            estimator_minus_one=estimator_bound,
        )

    states = zero_score_edge_states(tree, state)
    heights = orientation_heights(len(tree), states)
    powers = tuple(2**h for h in heights)

    # Genuine zero-score configurations have positive mass in every leaf-side
    # singleton branch, so no oriented edge can enter a leaf.  Hence leaves
    # have height zero.
    for v in range(len(tree)):
        if len(tree[v]) == 1 and heights[v] != 0:
            raise AssertionError("a tree leaf cannot have positive orientation height")

    weighted_mass = sum(powers[v] * state[v] for v in range(len(tree)))
    exact_edge_expansion = 0
    relaxed_edge_expansion = 0
    for edge in states:
        if edge.kind == "neutral":
            exact_edge_expansion += powers[edge.u] + powers[edge.v]
            relaxed_edge_expansion += powers[edge.u] + powers[edge.v]
        else:
            assert edge.tail is not None and edge.head is not None
            assert edge.parameter is not None
            k = edge.parameter
            exact_edge_expansion += powers[edge.tail] * (2 * k + 3) - powers[
                edge.head
            ] * k
            relaxed_edge_expansion += 3 * powers[edge.tail]
            if powers[edge.head] < 2 * powers[edge.tail]:
                raise AssertionError("height failed to double across an oriented edge")

    degree_height = sum(len(tree[v]) * powers[v] for v in range(len(tree)))
    leaf_term = sum(len(tree[v]) == 1 for v in range(len(tree)))
    internal_weights = tuple(
        len(tree[v]) if len(tree[v]) > 1 else 0 for v in range(len(tree))
    )
    internal_height = sum(internal_weights[v] * powers[v] for v in range(len(tree)))
    if degree_height != leaf_term + internal_height:
        raise AssertionError("leaf-height decomposition failed")

    parts = selected_height_partition(tree, states, heights)
    consolidated_root, consolidated = consolidate_connected_partition(
        tree, internal_weights, parts
    )
    root_values = [
        _potential(tree, internal_weights, range(len(tree)), root)
        for root in range(len(tree))
    ]
    maximum_root_internal = max(root_values)

    if weighted_mass != exact_edge_expansion:
        raise AssertionError("weighted vertex mass does not equal edge expansion")
    if not (
        mass
        <= weighted_mass
        <= exact_edge_expansion
        <= relaxed_edge_expansion
        <= degree_height
    ):
        raise AssertionError("zero-score dual inequality chain failed")
    if internal_height > consolidated:
        raise AssertionError("partition consolidation lost potential")
    if consolidated > maximum_root_internal:
        raise AssertionError("consolidated root exceeds maximum root potential")
    if leaf_term + maximum_root_internal != estimator_bound:
        raise AssertionError("root potential does not match estimator minus one")
    if mass > estimator_bound:
        raise AssertionError("zero-score estimator inequality failed")

    return ZeroScoreCertificate(
        mass=mass,
        heights=heights,
        weighted_mass=weighted_mass,
        exact_edge_expansion=exact_edge_expansion,
        relaxed_edge_expansion=relaxed_edge_expansion,
        degree_height_potential=degree_height,
        leaf_term=leaf_term,
        internal_height_potential=internal_height,
        consolidated_root=consolidated_root,
        consolidated_internal_potential=consolidated,
        maximum_root_internal_potential=maximum_root_internal,
        estimator_minus_one=estimator_bound,
    )
