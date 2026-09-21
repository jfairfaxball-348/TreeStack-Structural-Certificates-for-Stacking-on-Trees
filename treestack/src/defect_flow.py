"""Certificates for the full nonpositive-score estimator inequality.

The zero-score edge model has to be enlarged when some vertex scores are
negative.  This module implements the resulting defect-edge classification
and the weighted certificate used in ``notes/main-inequality.md``.

As everywhere in the structural solver, ``None`` is an empty branch and is
not interchangeable with the integer message zero.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from .estimator import estimate
from .generalized_flow import (
    EdgeState,
    consolidate_connected_partition,
    orientation_heights,
    selected_height_partition,
)
from .messages import EMPTY, directed_messages, scores
from .trees import Configuration, Tree, make_tree, validate_configuration


@dataclass(frozen=True)
class DefectEdgeState:
    """One edge state when both endpoint scores are nonpositive.

    ``kind`` is one of ``"neutral"``, ``"oriented"``, or ``"negative"``.
    An oriented state has a nonnegative message ``parameter`` from ``tail``
    to ``head``.  Its reverse message is
    ``-2*(parameter + defect[head])-3``.

    A negative state has messages ``-(2*r+1)`` from ``u`` to ``v`` and
    ``-(2*q+1)`` from ``v`` to ``u``.  The neutral state is the special case
    ``r=q=0`` and is represented separately.
    """

    u: int
    v: int
    kind: str
    tail: int | None = None
    head: int | None = None
    parameter: int | None = None
    augmented_parameter: int | None = None
    r: int | None = None
    q: int | None = None


@dataclass(frozen=True)
class DefectFlowCertificate:
    """Numerical chain certifying the arbitrary-defect estimator bound."""

    support_vertices: tuple[int, ...]
    support_configuration: Configuration
    support_scores: tuple[int, ...]
    owners: tuple[tuple[int, int], ...]
    heights: tuple[int, ...]
    weights: tuple[int, ...]
    mass: int
    weighted_mass: int
    exact_edge_expansion: int
    edge_excess: int
    defect_budget: int
    degree_height_potential: int
    configuration_slack: int
    leaf_slack_required: int
    compact_height_potential: int
    consolidated_root: int
    consolidated_internal_potential: int
    support_estimator_minus_one: int
    estimator_minus_one: int


def classify_defect_message_pair(
    u: int,
    v: int,
    a: int,
    b: int,
    defect_u: int,
    defect_v: int,
) -> DefectEdgeState:
    """Classify a genuine edge with endpoint defects ``defect_u, defect_v``.

    The caller supplies ``a=d_{u->v}`` and ``b=d_{v->u}``.  The equations
    being classified are

    ``a=F(-defect_u-b)`` and ``b=F(-defect_v-a)``.
    """
    if defect_u < 0 or defect_v < 0:
        raise ValueError("defects must be nonnegative")

    if a >= 0 and b >= 0:
        raise ValueError("both messages cannot be nonnegative")

    if a >= 0:
        expected_b = -2 * (a + defect_v) - 3
        if b != expected_b or defect_u not in (2 * defect_v, 2 * defect_v + 3):
            raise ValueError("messages do not satisfy an oriented defect state")
        if a == 0 and defect_u != 2 * defect_v:
            raise ValueError("message zero has only the input-three preimage")
        return DefectEdgeState(
            u=u,
            v=v,
            kind="oriented",
            tail=u,
            head=v,
            parameter=a,
            augmented_parameter=a + defect_v,
        )

    if b >= 0:
        state = classify_defect_message_pair(v, u, b, a, defect_v, defect_u)
        return DefectEdgeState(
            u=u,
            v=v,
            kind=state.kind,
            tail=state.tail,
            head=state.head,
            parameter=state.parameter,
            augmented_parameter=state.augmented_parameter,
        )

    if a % 2 == 0 or b % 2 == 0:
        raise ValueError("negative transfer values must be odd")
    r = (-a - 1) // 2
    q = (-b - 1) // 2
    if r < 0 or q < 0:
        raise ValueError("invalid negative-message parameters")
    if defect_u != r + 2 * q or defect_v != q + 2 * r:
        raise ValueError("messages do not satisfy a two-negative defect state")
    if r == 0 and q == 0:
        return DefectEdgeState(u=u, v=v, kind="neutral", r=0, q=0)
    return DefectEdgeState(u=u, v=v, kind="negative", r=r, q=q)


def _minimal_support_tree(
    tree: Tree, configuration: Configuration
) -> tuple[Tree, Configuration, tuple[int, ...]]:
    """Prune zero leaves to the minimal subtree spanning the support."""
    active = set(range(len(tree)))
    degree = [len(row) for row in tree]
    queue = deque(
        v for v in range(len(tree)) if degree[v] <= 1 and configuration[v] == 0
    )
    while queue and len(active) > 1:
        v = queue.popleft()
        if v not in active or configuration[v] != 0 or degree[v] > 1:
            continue
        active.remove(v)
        for u in tree[v]:
            if u in active:
                degree[u] -= 1
                if degree[u] <= 1 and configuration[u] == 0:
                    queue.append(u)

    vertices = tuple(sorted(active))
    relabel = {old: new for new, old in enumerate(vertices)}
    edges = [
        (relabel[u], relabel[v])
        for u in vertices
        for v in tree[u]
        if u < v and v in active
    ]
    reduced = make_tree(len(vertices), edges)
    state = tuple(configuration[v] for v in vertices)
    return reduced, state, vertices


def _defective_edge_owners(
    tree: Tree, defective_edges: set[int], endpoints: tuple[tuple[int, int], ...]
) -> dict[int, int]:
    """Injectively assign every edge of a forest to an incident vertex."""
    adjacency: list[list[tuple[int, int]]] = [[] for _ in tree]
    for index in defective_edges:
        u, v = endpoints[index]
        adjacency[u].append((v, index))
        adjacency[v].append((u, index))

    owners: dict[int, int] = {}
    seen: set[int] = set()
    for root in range(len(tree)):
        if root in seen or not adjacency[root]:
            continue
        seen.add(root)
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, index in adjacency[u]:
                if v in seen:
                    continue
                seen.add(v)
                queue.append(v)
                owners[index] = v

    if set(owners) != defective_edges:
        raise AssertionError("defective-edge owner assignment is incomplete")
    if len(set(owners.values())) != len(owners):
        raise AssertionError("defective-edge owners are not injective")
    return owners


def defect_flow_certificate(
    tree: Tree, configuration: Configuration
) -> DefectFlowCertificate:
    """Build the full estimator certificate for a nonzero non-stackable state.

    The input must have nonpositive structural score at every vertex and
    positive total mass.  Empty exterior branches are removed first; this is
    safe because their messages are ``EMPTY`` and hence omitted from every
    recursion and score on the minimal support subtree.
    """
    original = validate_configuration(tree, configuration)
    original_scores = scores(tree, original)
    if any(value > 0 for value in original_scores):
        raise ValueError("configuration has a positive structural score")
    if sum(original) == 0:
        raise ValueError("the all-zero configuration needs no defect certificate")

    support_tree, state, support_vertices = _minimal_support_tree(tree, original)
    if len(support_tree) < 2:
        raise AssertionError("a nonzero one-vertex support has positive score")
    support_scores = scores(support_tree, state)
    if support_scores != tuple(original_scores[v] for v in support_vertices):
        raise AssertionError("pruning empty branches changed a support score")
    if any(state[v] == 0 for v in range(len(state)) if len(support_tree[v]) == 1):
        raise AssertionError("every leaf of the minimal support tree is occupied")

    defects = tuple(-value for value in support_scores)
    messages = directed_messages(support_tree, state)
    if any(value is EMPTY for value in messages.values()):
        raise AssertionError("minimal support tree has an empty edge side")

    endpoints = tuple(
        (u, v)
        for u in range(len(support_tree))
        for v in support_tree[u]
        if u < v
    )
    edge_states: list[DefectEdgeState] = []
    defective_edges: set[int] = set()
    for index, (u, v) in enumerate(endpoints):
        a = messages[(u, v)]
        b = messages[(v, u)]
        assert a is not EMPTY and b is not EMPTY
        edge = classify_defect_message_pair(u, v, a, b, defects[u], defects[v])
        edge_states.append(edge)
        if edge.kind == "negative":
            defective_edges.add(index)
        elif edge.kind == "oriented":
            assert edge.head is not None
            if defects[edge.head] > 0:
                defective_edges.add(index)

    owners = _defective_edge_owners(support_tree, defective_edges, endpoints)

    oriented_states: list[EdgeState] = []
    edge_orientations: dict[int, tuple[int, int]] = {}
    for index, edge in enumerate(edge_states):
        if edge.kind == "oriented":
            assert edge.tail is not None and edge.head is not None
            tail, head = edge.tail, edge.head
            edge_orientations[index] = (tail, head)
            oriented_states.append(
                EdgeState(edge.u, edge.v, "oriented", tail, head, 0)
            )
        elif edge.kind == "negative":
            owner = owners[index]
            u, v = endpoints[index]
            tail, head = (v, u) if owner == u else (u, v)
            edge_orientations[index] = (tail, head)
            oriented_states.append(
                EdgeState(edge.u, edge.v, "oriented", tail, head, 0)
            )
        else:
            oriented_states.append(EdgeState(edge.u, edge.v, "neutral"))

    heights = orientation_heights(len(support_tree), oriented_states)
    weights = tuple(2**height for height in heights)
    weighted_mass = sum(weights[v] * state[v] for v in range(len(state)))
    defect_budget = sum(weights[v] * defects[v] for v in range(len(state)))

    exact_edge_expansion = 0
    edge_excess = 0
    for index, edge in enumerate(edge_states):
        u, v = endpoints[index]
        a = messages[(u, v)]
        b = messages[(v, u)]
        assert a is not EMPTY and b is not EMPTY
        exact_edge_expansion += -weights[v] * a - weights[u] * b

        if edge.kind == "neutral":
            continue
        tail, head = edge_orientations[index]
        if weights[head] < 2 * weights[tail]:
            raise AssertionError("weight failed to double across an orientation")

        if edge.kind == "oriented":
            assert edge.parameter is not None
            excess = 2 * weights[tail] * defects[head]
            k_term = edge.parameter * (2 * weights[tail] - weights[head])
            if k_term > 0:
                raise AssertionError("oriented parameter term is positive")
        else:
            message_tail = messages[(tail, head)]
            message_head = messages[(head, tail)]
            assert message_tail is not EMPTY and message_head is not EMPTY
            r = (-message_tail - 1) // 2
            q = (-message_head - 1) // 2
            excess = 2 * (weights[head] * r + weights[tail] * q)

        owner = owners.get(index)
        if excess > 0:
            if owner is None:
                raise AssertionError("positive edge excess has no owner")
            if excess > weights[owner] * defects[owner]:
                raise AssertionError("edge excess exceeds its owner's defect budget")
        edge_excess += excess

    if edge_excess > defect_budget:
        raise AssertionError("injective owners did not cover total edge excess")
    if weighted_mass != exact_edge_expansion - defect_budget:
        raise AssertionError("weighted score expansion failed")

    degree_height = sum(
        len(support_tree[v]) * weights[v] for v in range(len(support_tree))
    )
    if exact_edge_expansion > degree_height + edge_excess:
        raise AssertionError("edge expansion exceeds base potential plus excess")
    if weighted_mass > degree_height:
        raise AssertionError("defect cancellation failed to bound weighted mass")

    mass = sum(state)
    configuration_slack = sum(
        (weights[v] - 1) * state[v] for v in range(len(state))
    )
    if mass != weighted_mass - configuration_slack:
        raise AssertionError("configuration-weight slack identity failed")

    leaves = tuple(v for v in range(len(support_tree)) if len(support_tree[v]) == 1)
    leaf_slack_required = sum(weights[v] - 1 for v in leaves)
    if configuration_slack < leaf_slack_required:
        raise AssertionError("occupied support leaves did not pay the leaf slack")
    internal_weights = tuple(
        len(support_tree[v]) if len(support_tree[v]) > 1 else 0
        for v in range(len(support_tree))
    )
    compact_height = len(leaves) + sum(
        internal_weights[v] * weights[v] for v in range(len(support_tree))
    )
    if mass > compact_height:
        raise AssertionError("leaf slack did not produce the compact potential")

    parts = selected_height_partition(support_tree, oriented_states, heights)
    consolidated_root, consolidated = consolidate_connected_partition(
        support_tree, internal_weights, parts
    )
    support_bound = estimate(support_tree) - 1
    if len(leaves) + consolidated > support_bound:
        raise AssertionError("consolidated potential exceeds the support estimator")
    original_bound = estimate(tree) - 1
    if support_bound > original_bound:
        raise AssertionError("estimator decreased when the support tree was enlarged")
    if mass > original_bound:
        raise AssertionError("configuration exceeds the estimator bound")

    return DefectFlowCertificate(
        support_vertices=support_vertices,
        support_configuration=state,
        support_scores=support_scores,
        owners=tuple(sorted(owners.items())),
        heights=heights,
        weights=weights,
        mass=mass,
        weighted_mass=weighted_mass,
        exact_edge_expansion=exact_edge_expansion,
        edge_excess=edge_excess,
        defect_budget=defect_budget,
        degree_height_potential=degree_height,
        configuration_slack=configuration_slack,
        leaf_slack_required=leaf_slack_required,
        compact_height_potential=compact_height,
        consolidated_root=consolidated_root,
        consolidated_internal_potential=consolidated,
        support_estimator_minus_one=support_bound,
        estimator_minus_one=original_bound,
    )
