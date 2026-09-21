"""Command-line falsification search for the branch-message theorem."""

from __future__ import annotations

import argparse
from dataclasses import dataclass

import networkx as nx

from .enumerate import configurations
from .messages import scores
from .reachability import target_oracle
from .trees import make_tree


@dataclass(frozen=True)
class VerificationCount:
    trees: int = 0
    configurations: int = 0
    rooted_checks: int = 0


def verify(max_order: int, max_total: int) -> VerificationCount:
    """Exhaustively compare exact and structural solvers within a rectangle."""
    tree_count = configuration_count = rooted_count = 0
    for order in range(2, max_order + 1):
        for graph in nx.generators.nonisomorphic_trees(order):
            tree_count += 1
            tree = make_tree(order, graph.edges())
            oracles = [target_oracle(tree, root) for root in range(order)]
            for total in range(max_total + 1):
                for configuration in configurations(order, total):
                    configuration_count += 1
                    structural = scores(tree, configuration)
                    exact = tuple(oracle(configuration) for oracle in oracles)
                    predicted = tuple(score > 0 for score in structural)
                    rooted_count += order
                    if predicted != exact:
                        raise AssertionError(
                            "minimal encountered disagreement: "
                            f"tree={tree}, configuration={configuration}, "
                            f"score={structural}, exact={exact}"
                        )
    return VerificationCount(tree_count, configuration_count, rooted_count)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-order", type=int, default=6)
    parser.add_argument("--max-total", type=int, default=8)
    args = parser.parse_args()
    result = verify(args.max_order, args.max_total)
    print(
        f"verified {result.rooted_checks} rooted cases from "
        f"{result.configurations} configurations on {result.trees} trees"
    )


if __name__ == "__main__":
    main()
