from __future__ import annotations

import networkx as nx

from treestack.src.estimator import (
    extremal_configuration,
    obstruction_heights,
    root_estimate,
    sigma,
)
from treestack.src.messages import directed_messages, scores
from treestack.src.trees import make_tree


def test_extremal_sizes_and_zero_scores_through_order_10() -> None:
    expected_tree_counts = {2: 1, 3: 1, 4: 2, 5: 3, 6: 6, 7: 11, 8: 23, 9: 47, 10: 106}
    for order in range(2, 11):
        graphs = list(nx.generators.nonisomorphic_trees(order))
        assert len(graphs) == expected_tree_counts[order]
        for graph in graphs:
            tree = make_tree(order, graph.edges())
            for root in range(order):
                configuration = extremal_configuration(tree, root)
                heights = obstruction_heights(tree, root)
                messages = directed_messages(tree, configuration)
                assert sum(configuration) == root_estimate(tree, root) - 1
                assert configuration[root] == sigma(tree, root) - 1
                assert scores(tree, configuration) == (0,) * order
                for vertex, height in enumerate(heights):
                    if vertex == root:
                        assert height is None
                        continue
                    distance = nx.shortest_path_length(graph, root, vertex)
                    parent = next(
                        u
                        for u in tree[vertex]
                        if nx.shortest_path_length(graph, root, u) == distance - 1
                    )
                    assert messages[(vertex, parent)] == -height


def test_path_estimators_have_the_published_closed_form() -> None:
    from treestack.src.estimator import estimate

    for order in range(2, 16):
        path = make_tree(order, ((v, v + 1) for v in range(order - 1)))
        assert estimate(path) == 2**order - 1
