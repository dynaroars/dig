"""Exhaustive verification over explicitly finite manifest domains."""

from __future__ import annotations

import hashlib
from itertools import product
from typing import Any, Mapping

from ..aliases import alias_patterns
from ..model import Equation, Term, canonical_json, term_to_data
from ..outcomes import ComparisonKind, compare_outcomes, outcome_from_data
from ..spec import Manifest
from .base import ProofStatus, VerificationResult


class FiniteDomainVerifier:
    name = "dig-finite-domain"
    version = "1"

    def supports(self, manifest: Manifest, equation: Equation) -> tuple[bool, str]:
        declarations = {declaration["id"]: declaration for declaration in manifest.types}
        for type_id, _index in _variables(equation):
            if not declarations.get(type_id, {}).get("finite_values"):
                return False, f"type {type_id!r} has no explicit finite_values"
        return True, "all quantified variable types have explicit finite_values"

    def verify(
        self,
        worker,
        manifest: Manifest,
        equation: Equation,
        *,
        batch_cases: int = 100,
    ) -> VerificationResult:
        supported, detail = self.supports(manifest, equation)
        if not supported:
            return self._result(ProofStatus.UNKNOWN, 0, 0, 0, detail=detail)
        recipes = _all_recipes(manifest, equation)
        cases = []
        for recipe_index, recipe in enumerate(recipes):
            for side, term in (("lhs", equation.lhs), ("rhs", equation.rhs)):
                cases.append(
                    {
                        "case_id": f"r{recipe_index}-{side}",
                        "recipe": recipe,
                        "term": term_to_data(term),
                        "observe_roots": [root["id"] for root in recipe["roots"]],
                    }
                )
        raw_results: list[Mapping[str, Any]] = []
        for offset in range(0, len(cases), batch_cases):
            raw_results.extend(
                worker.evaluate_batch(
                    f"finite-proof-{offset // batch_cases}", cases[offset : offset + batch_cases]
                )
            )
        valid = 0
        invalid = 0
        for recipe_index, recipe in enumerate(recipes):
            lhs = outcome_from_data(raw_results[recipe_index * 2]["outcome"])
            rhs = outcome_from_data(raw_results[recipe_index * 2 + 1]["outcome"])
            comparison = compare_outcomes(lhs, rhs)
            if comparison.kind is ComparisonKind.COUNTEREXAMPLE:
                return self._result(
                    ProofStatus.REFUTED,
                    recipe_index + 1,
                    valid,
                    invalid,
                    counterexample={
                        "recipe": recipe,
                        "replay_id": "finite-domain-counterexample",
                    },
                    detail=comparison.detail,
                )
            if comparison.kind is ComparisonKind.ERROR:
                return self._result(
                    ProofStatus.ERROR,
                    recipe_index + 1,
                    valid,
                    invalid,
                    detail=comparison.detail,
                )
            if comparison.kind is ComparisonKind.INVALID_DOMAIN:
                invalid += 1
            else:
                valid += 1
        if not valid:
            return self._result(
                ProofStatus.UNKNOWN,
                len(recipes),
                valid,
                invalid,
                detail="the complete declared domain contains no common-domain case",
            )
        return self._result(
            ProofStatus.PROVED,
            len(recipes),
            valid,
            invalid,
            detail="complete declared finite domain exhausted",
        )

    def _result(
        self,
        status: ProofStatus,
        checked: int,
        valid: int,
        invalid: int,
        *,
        counterexample: dict[str, Any] | None = None,
        detail: str | None = None,
    ) -> VerificationResult:
        artifact = canonical_json(
            {
                "status": status.value,
                "verifier": self.name,
                "version": self.version,
                "scope": "finite-domain/common-defined-domain",
                "cases_checked": checked,
                "valid_cases": valid,
                "invalid_domain_cases": invalid,
                "counterexample": counterexample,
                "detail": detail,
            }
        )
        return VerificationResult(
            status=status,
            verifier=self.name,
            version=self.version,
            scope="finite-domain/common-defined-domain",
            cases_checked=checked,
            valid_cases=valid,
            invalid_domain_cases=invalid,
            assumptions=(
                "finite_values completely enumerate each quantified variable type",
                "both-side exceptions are outside the common defined domain",
            ),
            artifact_digest="sha256:" + hashlib.sha256(artifact.encode()).hexdigest(),
            counterexample=counterexample,
            detail=detail,
        )


def _variables(equation: Equation) -> tuple[tuple[str, int], ...]:
    found: set[tuple[str, int]] = set()

    def visit(term: Term) -> None:
        from ..model import Call, Variable

        if isinstance(term, Variable):
            found.add((term.type_id, term.index))
        elif isinstance(term, Call):
            for child in term.children:
                visit(child)

    visit(equation.lhs)
    visit(equation.rhs)
    return tuple(sorted(found))


def _all_recipes(manifest: Manifest, equation: Equation) -> tuple[dict[str, Any], ...]:
    declarations = {declaration["id"]: declaration for declaration in manifest.types}
    variables = _variables(equation)
    types = tuple(type_id for type_id, _index in variables)
    recipes: list[dict[str, Any]] = []
    for aliases in alias_patterns(types):
        root_types: dict[int, str] = {}
        for (type_id, _index), root in zip(variables, aliases, strict=True):
            root_types[root] = type_id
        roots = tuple(sorted(root_types))
        for values in product(*(declarations[root_types[root]]["finite_values"] for root in roots)):
            recipes.append(
                {
                    "recipe_id": f"finite-proof-{len(recipes):06d}",
                    "roots": [
                        {"id": f"r{root}", "type_id": root_types[root], "value": value}
                        for root, value in zip(roots, values, strict=True)
                    ],
                    "variables": [
                        {"type_id": type_id, "index": index, "root_id": f"r{root}"}
                        for (type_id, index), root in zip(variables, aliases, strict=True)
                    ],
                }
            )
    return tuple(recipes)

