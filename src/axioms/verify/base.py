"""Common verifier result contract."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Any


class ProofStatus(StrEnum):
    PROVED = "PROVED"
    REFUTED = "REFUTED"
    UNKNOWN = "UNKNOWN"
    ERROR = "ERROR"


@dataclass(frozen=True, slots=True)
class VerificationResult:
    status: ProofStatus
    verifier: str
    version: str
    scope: str
    cases_checked: int
    valid_cases: int
    invalid_domain_cases: int
    assumptions: tuple[str, ...]
    artifact_digest: str
    counterexample: dict[str, Any] | None = None
    detail: str | None = None

