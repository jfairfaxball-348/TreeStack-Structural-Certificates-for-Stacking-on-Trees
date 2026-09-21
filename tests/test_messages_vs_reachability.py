from __future__ import annotations

import networkx as nx
import pytest

from treestack.src.enumerate import configurations
from treestack.src.messages import scores
from treestack.src.reachability import maximum_at_target_oracle, target_oracle
from treestack.src.trees import make_tree


def nx_tree(graph: nx.Graph):
    return make_tree(graph.number_of_nodes(), graph.edges())


@pytest.mark.parametrize("order,max_total", [(2, 10), (3, 10), (4, 9), (5, 8), (6, 7)])
def test_messages_match_exact_reachability(order: int, max_total: int) -> None:
    for graph in nx.generators.nonisomorphic_trees(order):
        tree = nx_tree(graph)
        oracles = [target_oracle(tree, root) for root in range(order)]
        for total in range(max_total + 1):
            for configuration in configurations(order, total):
                structural = scores(tree, configuration)
                exact = tuple(oracle(configuration) for oracle in oracles)
                predicted = tuple(score > 0 for score in structural)
                assert predicted == exact, (tree, configuration, structural, exact)


def test_message_is_exact_boundary_gain_on_small_branches() -> None:
    """Test the stronger invariant: the best final boundary pile is q+d."""
    for order in range(2, 6):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree = nx_tree(graph)
            boundary = 0
            oracle = maximum_at_target_oracle(tree, boundary)
            for total in range(1, 8):
                for configuration in configurations(order - 1, total):
                    branch_state = (0,) + configuration
                    branch_score = scores(tree, branch_state)[boundary]
                    for q in range(7):
                        state = (q,) + configuration
                        expected = q + branch_score
                        if expected <= 0:
                            expected = 0
                        assert oracle(state) == expected, (
                            tree,
                            state,
                            branch_score,
                            oracle(state),
                        )
