"""Typed, deterministic, bottom-up term enumeration."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable, Mapping

from .model import (
    Call,
    Operation,
    PostStateProjection,
    ReturnProjection,
    Term,
    Variable,
    make_call,
    term_order_key,
)


@dataclass(frozen=True, slots=True)
class EnumerationResult:
    terms_by_type: Mapping[str, tuple[Term, ...]]
    truncated_types: frozenset[str]

    @property
    def terms(self) -> tuple[Term, ...]:
        return tuple(
            term
            for type_id in sorted(self.terms_by_type)
            for term in self.terms_by_type[type_id]
        )


def enumerate_terms(
    type_ids: Iterable[str],
    operations: Iterable[Operation],
    *,
    max_cost: int,
    variables_per_type: int = 2,
    max_terms_per_type: int = 1_000,
) -> EnumerationResult:
    """Enumerate well-typed terms up to ``max_cost`` with deterministic caps."""

    if max_cost < 0:
        raise ValueError("max_cost must be non-negative")
    if variables_per_type < 1:
        raise ValueError("variables_per_type must be positive")
    if max_terms_per_type < 1:
        raise ValueError("max_terms_per_type must be positive")

    ordered_types = tuple(sorted(set(type_ids)))
    known_types = frozenset(ordered_types)
    ordered_operations = tuple(sorted(operations, key=lambda operation: operation.id))
    for operation in ordered_operations:
        referenced = set(operation.input_types)
        if operation.return_type is not None:
            referenced.add(operation.return_type)
        missing = sorted(referenced - known_types)
        if missing:
            raise ValueError(f"operation {operation.id!r} references unknown types {missing}")

    exact: dict[int, dict[str, list[Term]]] = {
        0: {
            type_id: [Variable(type_id, index) for index in range(variables_per_type)]
            for type_id in ordered_types
        }
    }
    accepted: dict[str, list[Term]] = {type_id: [] for type_id in ordered_types}
    seen: dict[str, set[Term]] = {type_id: set() for type_id in ordered_types}
    truncated: set[str] = set()

    def add(term: Term, cost: int) -> None:
        bucket = accepted[term.type_id]
        if term in seen[term.type_id]:
            return
        if len(bucket) >= max_terms_per_type:
            truncated.add(term.type_id)
            return
        seen[term.type_id].add(term)
        bucket.append(term)
        exact.setdefault(cost, {}).setdefault(term.type_id, []).append(term)

    initial = exact.pop(0)
    exact[0] = {type_id: [] for type_id in ordered_types}
    for type_id in ordered_types:
        for term in initial[type_id]:
            add(term, 0)

    for cost in range(1, max_cost + 1):
        exact.setdefault(cost, {})
        candidates: list[Call] = []
        for operation in ordered_operations:
            remaining = cost - operation.cost
            if remaining < 0:
                continue
            child_choices = [
                [
                    term
                    for child_cost in range(remaining + 1)
                    for term in exact.get(child_cost, {}).get(type_id, ())
                ]
                for type_id in operation.input_types
            ]
            if any(not choices for choices in child_choices):
                continue
            projections = []
            if operation.return_type is not None:
                projections.append(ReturnProjection())
            projections.extend(PostStateProjection(index) for index in sorted(operation.mutates))
            for children in product(*child_choices):
                child_cost = sum(_known_cost(child, exact) for child in children)
                if child_cost != remaining:
                    continue
                for projection in projections:
                    candidates.append(make_call(operation, children, projection))
        for candidate in sorted(set(candidates), key=term_order_key):
            add(candidate, cost)

    return EnumerationResult(
        terms_by_type={
            type_id: tuple(sorted(terms, key=term_order_key))
            for type_id, terms in accepted.items()
        },
        truncated_types=frozenset(truncated),
    )


def _known_cost(term: Term, exact: Mapping[int, Mapping[str, list[Term]]]) -> int:
    for cost, by_type in exact.items():
        if term in by_type.get(term.type_id, ()):
            return cost
    raise ValueError("term was not found in the enumeration table")

