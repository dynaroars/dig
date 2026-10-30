"""Observational signatures and candidate extraction."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Mapping, Sequence

from .model import (
    Equation,
    Term,
    canonical_equation,
    canonical_json,
    term_order_key,
    thaw_encoded_value,
)
from .outcomes import ComparisonKind, Outcome, compare_outcomes


@dataclass(frozen=True, slots=True)
class Candidate:
    equation: Equation
    valid_samples: int
    invalid_domain_samples: int


@dataclass(frozen=True, slots=True)
class SignatureResult:
    candidates: tuple[Candidate, ...]
    insufficient_domain_pairs: int
    error_terms: tuple[Term, ...]


def outcome_signature(outcome: Outcome, *, same_exception: bool = False) -> str:
    """Normalize semantic output, excluding timing and other nondeterministic metadata."""

    if outcome.status.value == "returned":
        value = {
            "status": "returned",
            "return_value": thaw_encoded_value(outcome.return_value),
            "observations_by_root": {
                root_id: thaw_encoded_value(value)
                for root_id, value in (outcome.observations_by_root or ())
            },
            "aliases": list(outcome.aliases),
        }
    elif outcome.status.value == "threw":
        value = {"status": "threw"}
        if same_exception and outcome.exception is not None:
            value["exception"] = {
                "class": outcome.exception.class_name,
                "payload": thaw_encoded_value(outcome.exception.payload),
            }
    else:
        value = {"status": outcome.status.value}
    return canonical_json(value)


def discover_by_signatures(
    observations: Mapping[Term, Sequence[Outcome]],
    *,
    minimum_valid_samples: int,
    same_exception: bool = False,
) -> SignatureResult:
    """Group terms by behavior and emit equations to each smallest representative."""

    if minimum_valid_samples < 1:
        raise ValueError("minimum_valid_samples must be positive")
    error_terms = tuple(
        sorted(
            (
                term
                for term, outcomes in observations.items()
                if any(outcome.status.value not in {"returned", "threw"} for outcome in outcomes)
            ),
            key=term_order_key,
        )
    )
    errors = set(error_terms)
    groups: dict[tuple[str, tuple[str, ...]], list[Term]] = defaultdict(list)
    for term, outcomes in observations.items():
        if term in errors:
            continue
        signature = tuple(
            outcome_signature(outcome, same_exception=same_exception) for outcome in outcomes
        )
        groups[(term.type_id, signature)].append(term)

    candidates: list[Candidate] = []
    insufficient = 0
    for terms in groups.values():
        ordered = sorted(terms, key=term_order_key)
        representative = ordered[0]
        for term in ordered[1:]:
            comparisons = [
                compare_outcomes(lhs, rhs, same_exception_is_equivalent=same_exception)
                for lhs, rhs in zip(
                    observations[term], observations[representative], strict=True
                )
            ]
            if any(comparison.kind is ComparisonKind.ERROR for comparison in comparisons):
                continue
            valid = sum(
                comparison.kind is ComparisonKind.EQUIVALENT for comparison in comparisons
            )
            invalid = sum(
                comparison.kind is ComparisonKind.INVALID_DOMAIN for comparison in comparisons
            )
            if valid < minimum_valid_samples:
                insufficient += 1
                continue
            candidates.append(
                Candidate(canonical_equation(term, representative), valid, invalid)
            )
    candidates.sort(key=lambda candidate: canonical_json(candidate.equation))
    return SignatureResult(tuple(candidates), insufficient, error_terms)


def discover_by_pairwise_oracle(
    observations: Mapping[Term, Sequence[Outcome]], *, minimum_valid_samples: int
) -> tuple[Equation, ...]:
    """Small-grammar reference implementation used to test signature grouping."""

    terms = sorted(observations, key=term_order_key)
    equations: set[Equation] = set()
    for index, lhs in enumerate(terms):
        for rhs in terms[index + 1 :]:
            if lhs.type_id != rhs.type_id:
                continue
            comparisons = [
                compare_outcomes(left, right)
                for left, right in zip(observations[lhs], observations[rhs], strict=True)
            ]
            if any(
                comparison.kind in {ComparisonKind.COUNTEREXAMPLE, ComparisonKind.ERROR}
                for comparison in comparisons
            ):
                continue
            if sum(
                comparison.kind is ComparisonKind.EQUIVALENT for comparison in comparisons
            ) >= minimum_valid_samples:
                equations.add(canonical_equation(lhs, rhs))
    return tuple(sorted(equations, key=canonical_json))
