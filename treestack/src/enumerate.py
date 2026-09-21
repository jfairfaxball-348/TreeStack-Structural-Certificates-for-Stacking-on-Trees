"""Finite enumeration helpers for tests and bounded experiments."""

from __future__ import annotations

from typing import Iterator

from .trees import Configuration


def configurations(order: int, total: int) -> Iterator[Configuration]:
    """Yield all weak compositions of ``total`` into ``order`` entries."""
    if order < 1 or total < 0:
        return
    if order == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for suffix in configurations(order - 1, total - first):
            yield (first,) + suffix

