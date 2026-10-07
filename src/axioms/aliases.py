"""Deterministic canonical alias-pattern generation."""

from __future__ import annotations

from collections.abc import Iterator, Sequence


def alias_patterns(type_ids: Sequence[str]) -> Iterator[tuple[int, ...]]:
    """Yield canonical root assignments; only equal types may alias.

    Root numbers are assigned by first occurrence, so raw renamings are never
    generated. For ``("stack", "stack")`` the results are ``(0, 0)`` and
    ``(0, 1)``.
    """

    if not type_ids:
        yield ()
        return

    assignment: list[int] = []
    roots_by_type: dict[str, list[int]] = {}
    next_root = 0

    def visit(position: int, available: dict[str, list[int]], fresh: int) -> Iterator[tuple[int, ...]]:
        if position == len(type_ids):
            yield tuple(assignment)
            return
        type_id = type_ids[position]
        for root in available.get(type_id, ()):
            assignment.append(root)
            yield from visit(position + 1, available, fresh)
            assignment.pop()

        assignment.append(fresh)
        updated = {key: list(value) for key, value in available.items()}
        updated.setdefault(type_id, []).append(fresh)
        yield from visit(position + 1, updated, fresh + 1)
        assignment.pop()

    yield from visit(0, roots_by_type, next_root)

