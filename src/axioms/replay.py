"""Equation replay and greedy deterministic counterexample minimization."""

from __future__ import annotations

from typing import Any, Mapping

from .model import Equation, term_to_data
from .outcomes import ComparisonKind, compare_outcomes, outcome_from_data
from .shrink import shrink_recipe


def replay_equation(worker, equation: Equation, recipe: Mapping[str, Any], replay_id: str):
    roots = [root["id"] for root in recipe.get("roots", ())]
    cases = [
        {
            "case_id": f"{replay_id}-{side}",
            "recipe": recipe,
            "term": term_to_data(term),
            "observe_roots": roots,
        }
        for side, term in (("lhs", equation.lhs), ("rhs", equation.rhs))
    ]
    raw = worker.evaluate_batch(replay_id, cases)
    lhs = outcome_from_data(raw[0]["outcome"])
    rhs = outcome_from_data(raw[1]["outcome"])
    return compare_outcomes(lhs, rhs), raw[0]["outcome"], raw[1]["outcome"]


def minimize_counterexample(
    worker,
    equation: Equation,
    recipe: Mapping[str, Any],
    *,
    max_attempts: int = 1_000,
) -> dict[str, Any]:
    """Greedily keep the first shrink move that still refutes the equation."""

    current = dict(recipe)
    attempts = 0
    while attempts < max_attempts:
        improved = False
        for candidate in shrink_recipe(current):
            attempts += 1
            comparison, _lhs, _rhs = replay_equation(
                worker, equation, candidate, f"shrink-{attempts}"
            )
            if comparison.kind is ComparisonKind.COUNTEREXAMPLE:
                current = candidate
                improved = True
                break
            if attempts >= max_attempts:
                break
        if not improved:
            break
    comparison, lhs, rhs = replay_equation(worker, equation, current, "shrink-final")
    if comparison.kind is not ComparisonKind.COUNTEREXAMPLE:
        raise ValueError("the supplied recipe is not a reproducible counterexample")
    return {
        "recipe": current,
        "replay_id": "minimized-counterexample",
        "lhs_outcome": lhs,
        "rhs_outcome": rhs,
    }
