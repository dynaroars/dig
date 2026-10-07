"""Replay-based determinism checks for target terms."""

from __future__ import annotations

from typing import Any, Mapping

from .model import Term, term_to_data
from .outcomes import outcome_from_data
from .signatures import outcome_signature


def replay_is_deterministic(
    worker,
    term: Term,
    recipe: Mapping[str, Any],
    *,
    replays: int = 3,
) -> bool:
    if replays < 2:
        raise ValueError("determinism checking requires at least two replays")
    cases = [
        {
            "case_id": f"replay-{index}",
            "recipe": recipe,
            "term": term_to_data(term),
            "observe_roots": [root["id"] for root in recipe.get("roots", ())],
        }
        for index in range(replays)
    ]
    outcomes = worker.evaluate_batch("determinism", cases)
    signatures = {
        outcome_signature(outcome_from_data(result["outcome"])) for result in outcomes
    }
    return len(signatures) == 1
