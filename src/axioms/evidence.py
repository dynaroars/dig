"""Evidence, verdicts, and deterministic seed derivation."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
import hashlib
from typing import Any

from .model import Equation, equation_to_data, format_equation


class Verdict(StrEnum):
    REFUTED = "REFUTED"
    CANDIDATE = "CANDIDATE"
    VALIDATED = "VALIDATED"
    PROVED = "PROVED"
    ERROR = "ERROR"


@dataclass(frozen=True, slots=True)
class SampleCounts:
    valid: int = 0
    invalid_domain: int = 0
    exceptions: int = 0
    failed: int = 0

    def to_data(self) -> dict[str, int]:
        return {
            "valid": self.valid,
            "invalid_domain": self.invalid_domain,
            "exceptions": self.exceptions,
            "failed": self.failed,
        }


@dataclass(frozen=True, slots=True)
class Finding:
    id: str
    equation: Equation
    verdict: Verdict
    discovery: SampleCounts
    validation: SampleCounts
    generator_ids: tuple[str, ...]
    observer_ids: tuple[str, ...]
    exception_policy: str
    truncated: bool
    counterexample: dict[str, Any] | None = None
    proof: dict[str, Any] | None = None

    def to_data(self) -> dict[str, Any]:
        evidence: dict[str, Any] = {
            "discovery": self.discovery.to_data(),
            "validation": self.validation.to_data(),
            "generator_ids": list(self.generator_ids),
            "observer_ids": list(self.observer_ids),
            "exception_policy": self.exception_policy,
            "truncated": self.truncated,
        }
        if self.counterexample is not None:
            evidence["counterexample"] = self.counterexample
        if self.proof is not None:
            evidence["proof"] = self.proof
        return {
            "id": self.id,
            "text": format_equation(self.equation),
            "equation": equation_to_data(self.equation),
            "verdict": self.verdict.value,
            "evidence": evidence,
        }


def derive_seed(root_seed: int, stream: str) -> int:
    if root_seed < 0:
        raise ValueError("root seed must be non-negative")
    digest = hashlib.sha256(f"dig-axioms-v1\0{root_seed}\0{stream}".encode()).digest()
    return int.from_bytes(digest[:8], "big")


def split_seeds(root_seed: int) -> dict[str, int]:
    return {
        "root": root_seed,
        **{
            name: derive_seed(root_seed, name)
            for name in ("discovery", "validation", "shrinking", "mutation")
        },
    }
