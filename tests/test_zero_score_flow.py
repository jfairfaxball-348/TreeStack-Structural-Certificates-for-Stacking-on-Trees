from __future__ import annotations

from itertools import product

import networkx as nx
import pytest

from treestack.src.enumerate import configurations
from treestack.src.estimator import estimate, extremal_configuration, root_estimate
from treestack.src.generalized_flow import (
    EdgeState,
    classify_message_pair,
    consolidate_connected_partition,
    orientation_heights,
    selected_height_partition,
    zero_score_certificate,
    zero_score_edge_states,
)
from treestack.src.messages import EMPTY, directed_messages, scores, transfer
from treestack.src.trees import make_tree


def nx_tree(graph: nx.Graph):
    return make_tree(graph.number_of_nodes(), graph.edges())


def test_integer_edge_state_classification_is_complete_on_large_window() -> None:
    solutions = []
    for a in range(-80, 81):
        for b in range(-80, 81):
            if a == transfer(-b) and b == transfer(-a):
                state = classify_message_pair(0, 1, a, b)
                solutions.append((a, b))
                if state.kind == "neutral":
                    assert (a, b) == (-1, -1)
                elif state.tail == 0:
                    assert a >= 0 and b == -2 * a - 3
                else:
                    assert b >= 0 and a == -2 * b - 3
    expected = {(-1, -1)}
    expected.update((k, -2 * k - 3) for k in range(39))
    expected.update((-2 * k - 3, k) for k in range(39))
    assert expected.issubset(set(solutions))


def test_empty_branch_is_not_a_zero_message_edge_state() -> None:
    edge = make_tree(2, [(0, 1)])
    messages = directed_messages(edge, (3, 0))
    assert messages[(0, 1)] == 0
    assert messages[(1, 0)] is EMPTY
    assert scores(edge, (3, 0)) == (3, 0)
    with pytest.raises(ValueError):
        zero_score_edge_states(edge, (3, 0))


def test_zero_score_certificate_on_all_small_zero_score_configurations() -> None:
    for order in range(2, 5):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree = nx_tree(graph)
            bound = min(estimate(tree) - 1, 12)
            for total in range(bound + 1):
                for configuration in configurations(order, total):
                    if scores(tree, configuration) == (0,) * order:
                        certificate = zero_score_certificate(tree, configuration)
                        assert certificate.mass == total
                        assert certificate.mass <= certificate.estimator_minus_one


def test_explicit_zero_score_extremizers_have_tight_certificate_through_order_10() -> None:
    for order in range(2, 11):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree = nx_tree(graph)
            for root in range(order):
                configuration = extremal_configuration(tree, root)
                certificate = zero_score_certificate(tree, configuration)
                assert certificate.mass == root_estimate(tree, root) - 1
                assert certificate.mass <= certificate.estimator_minus_one


def test_nonunique_star_extremizer_is_tight() -> None:
    star = make_tree(4, [(0, 1), (0, 2), (0, 3)])
    configuration = (0, 3, 3, 3)
    assert scores(star, configuration) == (0, 0, 0, 0)
    certificate = zero_score_certificate(star, configuration)
    assert certificate.mass == certificate.estimator_minus_one == 9


def test_height_partition_consolidation_for_all_orientations_through_order_8() -> None:
    """Independent finite check of the k-free combinatorial proof step."""
    for order in range(2, 9):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree = nx_tree(graph)
            edges = [(u, v) for u, v in graph.edges()]
            weights = tuple(len(tree[v]) if len(tree[v]) > 1 else 0 for v in range(order))
            for choices in product(range(3), repeat=len(edges)):
                states = []
                for (u, v), choice in zip(edges, choices):
                    if choice == 0:
                        states.append(EdgeState(u, v, "neutral"))
                    elif choice == 1:
                        states.append(EdgeState(u, v, "oriented", u, v, 0))
                    else:
                        states.append(EdgeState(u, v, "oriented", v, u, 0))
                heights = orientation_heights(order, states)
                parts = selected_height_partition(tree, states, heights)
                root, consolidated = consolidate_connected_partition(tree, weights, parts)
                internal_height = sum(weights[v] * 2 ** heights[v] for v in range(order))
                assert consolidated >= internal_height
                assert 0 <= root < order
