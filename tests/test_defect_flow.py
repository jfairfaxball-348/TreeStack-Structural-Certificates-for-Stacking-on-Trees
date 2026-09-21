from __future__ import annotations

import networkx as nx

from treestack.src.defect_flow import (
    classify_defect_message_pair,
    defect_flow_certificate,
)
from treestack.src.enumerate import configurations
from treestack.src.estimator import estimate
from treestack.src.messages import directed_messages, scores, transfer
from treestack.src.reachability import stackable
from treestack.src.trees import make_tree


def nx_tree(graph: nx.Graph):
    return make_tree(graph.number_of_nodes(), graph.edges())


def test_defect_edge_classification_on_a_large_finite_window() -> None:
    for defect_u in range(13):
        for defect_v in range(13):
            for a in range(-50, 21):
                for b in range(-50, 21):
                    if a != transfer(-defect_u - b):
                        continue
                    if b != transfer(-defect_v - a):
                        continue
                    edge = classify_defect_message_pair(
                        0, 1, a, b, defect_u, defect_v
                    )
                    if edge.kind == "neutral":
                        assert (a, b, defect_u, defect_v) == (-1, -1, 0, 0)
                    elif edge.kind == "oriented":
                        assert (a >= 0) != (b >= 0)
                    else:
                        assert a < 0 and b < 0
                        assert edge.r != 0 or edge.q != 0


def test_defect_certificate_on_all_bounded_nonpositive_score_states() -> None:
    checked = 0
    for order in range(2, 6):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree = nx_tree(graph)
            for total in range(1, 13):
                for configuration in configurations(order, total):
                    if max(scores(tree, configuration)) <= 0:
                        certificate = defect_flow_certificate(tree, configuration)
                        assert certificate.mass == total
                        assert certificate.mass <= certificate.estimator_minus_one
                        assert certificate.estimator_minus_one == estimate(tree) - 1
                        checked += 1
    assert checked == 2917


def test_empty_exterior_branch_is_pruned_before_defect_classification() -> None:
    star = make_tree(4, [(0, 1), (0, 2), (0, 3)])
    configuration = (0, 3, 3, 0)
    assert scores(star, configuration) == (0, 0, 0, -3)
    certificate = defect_flow_certificate(star, configuration)
    assert certificate.support_vertices == (0, 1, 2)
    assert certificate.support_configuration == (0, 3, 3)
    assert certificate.support_scores == (0, 0, 0)
    assert certificate.mass == 6
    assert certificate.support_estimator_minus_one == 6
    assert certificate.estimator_minus_one == 9


def test_coordinatewise_saturation_fails_on_the_four_vertex_path() -> None:
    path = make_tree(4, [(1, 0), (1, 2), (0, 3)])
    configuration = (1, 3, 0, 1)
    assert scores(path, configuration) == (0, 0, -3, 0)
    assert not stackable(path, configuration)
    for vertex in range(4):
        augmented = list(configuration)
        augmented[vertex] += 1
        augmented_state = tuple(augmented)
        assert max(scores(path, augmented_state)) > 0
        assert stackable(path, augmented_state)


def test_naive_edgewise_zero_state_replacement_can_make_negative_counts() -> None:
    path = make_tree(4, [(1, 0), (1, 2), (0, 3)])
    configuration = (0, 0, 1, 2)
    score = scores(path, configuration)
    assert score == (-4, -2, -4, -11)
    defects = tuple(-value for value in score)
    messages = directed_messages(path, configuration)
    replacement = {}

    for u in range(len(path)):
        for v in path[u]:
            if u >= v:
                continue
            a = messages[(u, v)]
            b = messages[(v, u)]
            assert a is not None and b is not None
            edge = classify_defect_message_pair(u, v, a, b, defects[u], defects[v])
            if edge.kind == "oriented":
                assert edge.tail is not None and edge.head is not None
                assert edge.augmented_parameter is not None
                k = edge.augmented_parameter
                replacement[(edge.tail, edge.head)] = k
                replacement[(edge.head, edge.tail)] = -2 * k - 3
            else:
                replacement[(u, v)] = -1
                replacement[(v, u)] = -1

    formal_counts = tuple(
        -sum(replacement[(u, v)] for u in path[v]) for v in range(len(path))
    )
    assert formal_counts == (-4, 2, 1, 13)
