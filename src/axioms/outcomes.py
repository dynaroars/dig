"""Normalized execution outcomes and default comparison semantics."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Any, Mapping

from .model import freeze_encoded_value, thaw_encoded_value


class OutcomeStatus(StrEnum):
    RETURNED = "returned"
    THREW = "threw"
    TIMED_OUT = "timed_out"
    CRASHED = "crashed"
    PROTOCOL_ERROR = "protocol_error"
    UNSUPPORTED = "unsupported"


class ComparisonKind(StrEnum):
    EQUIVALENT = "equivalent"
    COUNTEREXAMPLE = "counterexample"
    INVALID_DOMAIN = "invalid_domain"
    ERROR = "error"


@dataclass(frozen=True, slots=True)
class NormalizedException:
    class_name: str
    payload: Any = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "payload", freeze_encoded_value(self.payload))


@dataclass(frozen=True, slots=True)
class Outcome:
    status: OutcomeStatus
    return_value: Any = None
    observations_by_root: Mapping[str, Any] | None = None
    aliases: tuple[tuple[str, str], ...] = ()
    exception: NormalizedException | None = None

    def __post_init__(self) -> None:
        if self.status is OutcomeStatus.THREW and self.exception is None:
            raise ValueError("a thrown outcome requires an exception")
        if self.status is not OutcomeStatus.THREW and self.exception is not None:
            raise ValueError("only a thrown outcome may contain an exception")
        object.__setattr__(self, "return_value", freeze_encoded_value(self.return_value))
        observations = self.observations_by_root or {}
        object.__setattr__(
            self,
            "observations_by_root",
            tuple(
                sorted(
                    (root_id, freeze_encoded_value(value))
                    for root_id, value in observations.items()
                )
            ),
        )


@dataclass(frozen=True, slots=True)
class OutcomeComparison:
    kind: ComparisonKind
    detail: str


def compare_outcomes(
    lhs: Outcome, rhs: Outcome, *, same_exception_is_equivalent: bool = False
) -> OutcomeComparison:
    infrastructure = {
        OutcomeStatus.TIMED_OUT,
        OutcomeStatus.CRASHED,
        OutcomeStatus.PROTOCOL_ERROR,
        OutcomeStatus.UNSUPPORTED,
    }
    if lhs.status in infrastructure or rhs.status in infrastructure:
        return OutcomeComparison(ComparisonKind.ERROR, f"{lhs.status} versus {rhs.status}")
    if lhs.status is OutcomeStatus.THREW and rhs.status is OutcomeStatus.THREW:
        if same_exception_is_equivalent and lhs.exception == rhs.exception:
            return OutcomeComparison(ComparisonKind.EQUIVALENT, "same normalized exception")
        return OutcomeComparison(ComparisonKind.INVALID_DOMAIN, "both sides threw")
    if lhs.status is OutcomeStatus.THREW or rhs.status is OutcomeStatus.THREW:
        return OutcomeComparison(ComparisonKind.COUNTEREXAMPLE, "only one side threw")
    if lhs.return_value != rhs.return_value:
        return OutcomeComparison(ComparisonKind.COUNTEREXAMPLE, "return values differ")
    if dict(lhs.observations_by_root or {}) != dict(rhs.observations_by_root or {}):
        return OutcomeComparison(ComparisonKind.COUNTEREXAMPLE, "observed post-state differs")
    if lhs.aliases != rhs.aliases:
        return OutcomeComparison(ComparisonKind.COUNTEREXAMPLE, "observable aliases differ")
    return OutcomeComparison(ComparisonKind.EQUIVALENT, "return and observable state agree")


def outcome_from_data(data: Mapping[str, Any]) -> Outcome:
    """Decode the semantic fields of a worker outcome."""

    try:
        status = OutcomeStatus(data["status"])
    except (KeyError, ValueError) as exc:
        raise ValueError("worker outcome has an invalid status") from exc
    raw_exception = data.get("exception")
    exception = None
    if raw_exception is not None:
        if not isinstance(raw_exception, Mapping) or not isinstance(
            raw_exception.get("class"), str
        ):
            raise ValueError("worker exception must contain a class")
        exception = NormalizedException(raw_exception["class"], raw_exception.get("payload"))
    observations = data.get("observations_by_root", {})
    if not isinstance(observations, Mapping):
        raise ValueError("worker observations_by_root must be an object")
    normalized_observations = {
        root_id: value.get("value")
        if isinstance(value, Mapping) and "value" in value
        else value
        for root_id, value in observations.items()
    }
    aliases = data.get("aliases", ())
    if not isinstance(aliases, list) or any(
        not isinstance(pair, list) or len(pair) != 2 for pair in aliases
    ):
        raise ValueError("worker aliases must be pairs")
    return Outcome(
        status=status,
        return_value=data.get("return_value"),
        observations_by_root=normalized_observations,
        aliases=tuple((pair[0], pair[1]) for pair in aliases),
        exception=exception,
    )
