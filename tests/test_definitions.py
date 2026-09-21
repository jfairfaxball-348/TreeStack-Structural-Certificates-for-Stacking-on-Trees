from treestack.src.estimator import estimate, root_estimate, sigma
from treestack.src.messages import EMPTY, directed_messages, transfer
from treestack.src.trees import make_tree


def test_transfer_edge_cases() -> None:
    assert [transfer(x) for x in range(-2, 9)] == [-7, -5, -3, -1, 1, 0, 2, 1, 3, 2, 4]


def test_empty_message_is_not_integer_zero() -> None:
    edge = make_tree(2, [(0, 1)])
    assert directed_messages(edge, (0, 0))[(0, 1)] is EMPTY
    assert directed_messages(edge, (3, 0))[(0, 1)] == 0


def test_paper_sigma_includes_one() -> None:
    edge = make_tree(2, [(0, 1)])
    assert sigma(edge, 0) == 2
    assert root_estimate(edge, 0) == 3
    assert estimate(edge) == 3

