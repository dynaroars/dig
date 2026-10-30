"""Language-neutral discovery and held-out validation orchestration."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from pathlib import Path
import sys
from typing import Any, Iterable, Mapping, Sequence

from .enumerate import EnumerationResult, enumerate_terms
from .evidence import Finding, SampleCounts, Verdict, derive_seed, split_seeds
from .model import Equation, Term, canonical_json, equation_to_data, term_to_data
from .outcomes import ComparisonKind, Outcome, compare_outcomes, outcome_from_data
from .recipes import recipe_key, sampled_recipes
from .replay import minimize_counterexample
from .robustness import replay_is_deterministic
from .signatures import Candidate, discover_by_signatures
from .spec import Manifest, load_manifest
from .workers.python_worker import PythonWorker
from .workers.jvm_worker import JavaWorker


@dataclass(frozen=True, slots=True)
class EngineConfig:
    max_call_cost: int = 3
    variables_per_type: int = 2
    max_terms_per_type: int = 1_000
    discovery_tests: int = 100
    validation_tests: int = 1_000
    minimum_valid_samples: int = 20
    batch_cases: int = 100
    root_seed: int = 42
    determinism_replays: int = 2


@dataclass(frozen=True, slots=True)
class AxiomRun:
    manifest: Manifest
    config: EngineConfig
    seeds: Mapping[str, int]
    enumeration: EnumerationResult
    findings: tuple[Finding, ...]
    diagnostics: tuple[dict[str, str], ...]
    target_fingerprint: str

    def to_data(self) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "analysis_kind": "axioms",
            "run_id": f"axioms-{self.target_fingerprint[7:19]}",
            "language": self.manifest.language,
            "target_fingerprint": self.target_fingerprint,
            "seeds": dict(self.seeds),
            "limits": {
                "max_call_cost": self.config.max_call_cost,
                "variables_per_type": self.config.variables_per_type,
                "max_terms_per_type": self.config.max_terms_per_type,
                "max_candidates": self.manifest.limits["max_candidates"],
                "discovery_tests": self.config.discovery_tests,
                "validation_tests": self.config.validation_tests,
                "minimum_valid_samples": self.config.minimum_valid_samples,
                "case_timeout_ms": self.manifest.limits["case_timeout_ms"],
                "batch_timeout_ms": self.manifest.limits["batch_timeout_ms"],
                "worker_memory_mib": self.manifest.limits["worker_memory_mib"],
                "output_limit_bytes": self.manifest.limits["output_limit_bytes"],
            },
            "findings": [finding.to_data() for finding in self.findings],
            "diagnostics": list(self.diagnostics),
        }


def run_python_finite(
    manifest_path: Path | str,
    config: EngineConfig = EngineConfig(),
    *,
    python_executable: Path | str | None = None,
    worker_timeout: float | None = None,
) -> AxiomRun:
    """Run discovery/validation over explicitly finite recipes in a Python worker."""

    manifest = load_manifest(manifest_path)
    if manifest.language != "python":
        raise ValueError("run_python_finite requires a Python manifest")
    return _run_finite(manifest, config, lambda: PythonWorker(
        manifest.source,
        python_executable=python_executable or sys.executable,
        timeout=worker_timeout or manifest.limits["batch_timeout_ms"] / 1000,
    ))


def run_java_finite(
    manifest_path: Path | str,
    config: EngineConfig = EngineConfig(),
    *,
    java_executable: Path | str = "java",
    javac_executable: Path | str = "javac",
    compiler_environment: Mapping[str, str] | None = None,
) -> AxiomRun:
    manifest = load_manifest(manifest_path)
    if manifest.language != "java":
        raise ValueError("run_java_finite requires a Java manifest")
    return _run_finite(manifest, config, lambda: JavaWorker(
        manifest.source,
        java_executable=java_executable,
        javac_executable=javac_executable,
        timeout=manifest.limits["batch_timeout_ms"] / 1000,
        compiler_environment=compiler_environment,
    ))


def _run_finite(manifest: Manifest, config: EngineConfig, worker_factory) -> AxiomRun:
    if config.minimum_valid_samples > min(
        config.discovery_tests, config.validation_tests
    ):
        raise ValueError("minimum_valid_samples exceeds a campaign size")
    if config.determinism_replays < 2:
        raise ValueError("determinism_replays must be at least two")
    seeds = split_seeds(config.root_seed)
    operations = manifest.model_operations()
    type_ids = tuple(declaration["id"] for declaration in manifest.types)
    enumeration = enumerate_terms(
        type_ids,
        operations,
        max_cost=config.max_call_cost,
        variables_per_type=config.variables_per_type,
        max_terms_per_type=config.max_terms_per_type,
    )
    variable_counts = {type_id: config.variables_per_type for type_id in type_ids}
    with worker_factory() as worker:
        declarations = {declaration["id"]: declaration for declaration in manifest.types}
        values_by_type: dict[str, list[Any]] = {}
        requested_values = max(32, config.discovery_tests + config.validation_tests)
        for type_id in type_ids:
            finite_values = declarations[type_id].get("finite_values")
            if finite_values:
                values_by_type[type_id] = list(finite_values)
            elif declarations[type_id].get("generator") and hasattr(worker, "generate_values"):
                values_by_type[type_id] = worker.generate_values(
                    type_id,
                    seed=derive_seed(seeds["discovery"], f"generator:{type_id}"),
                    count=requested_values,
                )
            else:
                raise ValueError(
                    f"type {type_id!r} needs finite_values or a supported recipe generator"
                )
        discovery_recipes = sampled_recipes(
            values_by_type,
            variable_counts,
            seed=seeds["discovery"],
            limit=config.discovery_tests,
        )
        discovery_keys = {recipe_key(recipe) for recipe in discovery_recipes}
        validation_recipes = sampled_recipes(
            values_by_type,
            variable_counts,
            seed=seeds["validation"],
            limit=config.validation_tests,
            exclude=discovery_keys,
        )
        if len(discovery_recipes) < config.discovery_tests or len(validation_recipes) < config.validation_tests:
            raise ValueError(
                f"recipe pools cannot provide {config.discovery_tests} discovery and "
                f"{config.validation_tests} distinct validation recipes"
            )
        discovery_observations = _evaluate_terms(
            worker,
            enumeration.terms,
            discovery_recipes,
            batch_cases=config.batch_cases,
            batch_prefix="discovery",
        )
        discovered = discover_by_signatures(
            discovery_observations,
            minimum_valid_samples=config.minimum_valid_samples,
        )
        candidate_terms = {
            term
            for candidate in discovered.candidates
            for term in (candidate.equation.lhs, candidate.equation.rhs)
        }
        validation_observations = _evaluate_terms(
            worker,
            tuple(candidate_terms),
            validation_recipes,
            batch_cases=config.batch_cases,
            batch_prefix="validation",
        )
        nondeterministic_terms = {
            term
            for term in candidate_terms
            if not replay_is_deterministic(
                worker,
                term,
                validation_recipes[0],
                replays=config.determinism_replays,
            )
        }

        findings = tuple(
            _validate_candidate(
                worker,
                index,
                candidate,
                discovery_observations,
                validation_observations,
                validation_recipes,
                manifest,
                bool(enumeration.truncated_types),
                config.minimum_valid_samples,
                nondeterministic_terms,
            )
            for index, candidate in enumerate(discovered.candidates, start=1)
        )
    diagnostics: list[dict[str, str]] = []
    if enumeration.truncated_types:
        diagnostics.append(
            {
                "severity": "warning",
                "code": "term-limit-reached",
                "message": "term enumeration was truncated for: "
                + ", ".join(sorted(enumeration.truncated_types)),
            }
        )
    if discovered.insufficient_domain_pairs:
        diagnostics.append(
            {
                "severity": "info",
                "code": "insufficient-valid-domain",
                "message": f"{discovered.insufficient_domain_pairs} observational pair(s) "
                "did not meet the minimum valid sample count",
            }
        )
    if nondeterministic_terms:
        diagnostics.append(
            {
                "severity": "error",
                "code": "nondeterministic-operation",
                "message": f"{len(nondeterministic_terms)} candidate term(s) changed on replay",
            }
        )
    return AxiomRun(
        manifest=manifest,
        config=config,
        seeds=seeds,
        enumeration=enumeration,
        findings=findings,
        diagnostics=tuple(diagnostics),
        target_fingerprint=_fingerprint_target(manifest),
    )


def _evaluate_terms(
    worker,
    terms: Sequence[Term],
    recipes: Sequence[Mapping[str, Any]],
    *,
    batch_cases: int,
    batch_prefix: str,
) -> dict[Term, tuple[Outcome, ...]]:
    ordered_terms = tuple(sorted(terms, key=canonical_json))
    cases = [
        {
            "case_id": f"t{term_index}-r{recipe_index}",
            "recipe": recipe,
            "term": term_to_data(term),
            "observe_roots": [root["id"] for root in recipe["roots"]],
        }
        for term_index, term in enumerate(ordered_terms)
        for recipe_index, recipe in enumerate(recipes)
    ]
    results: list[Mapping[str, Any]] = []
    for offset in range(0, len(cases), batch_cases):
        results.extend(
            worker.evaluate_batch(
                f"{batch_prefix}-{offset // batch_cases}", cases[offset : offset + batch_cases]
            )
        )
    return {
        term: tuple(
            outcome_from_data(results[term_index * len(recipes) + recipe_index]["outcome"])
            for recipe_index in range(len(recipes))
        )
        for term_index, term in enumerate(ordered_terms)
    }


def _validate_candidate(
    worker,
    index: int,
    candidate: Candidate,
    discovery: Mapping[Term, Sequence[Outcome]],
    validation: Mapping[Term, Sequence[Outcome]],
    validation_recipes: Sequence[Mapping[str, Any]],
    manifest: Manifest,
    truncated: bool,
    minimum_valid_samples: int,
    nondeterministic_terms: set[Term],
) -> Finding:
    equation = candidate.equation
    comparisons = [
        compare_outcomes(lhs, rhs)
        for lhs, rhs in zip(validation[equation.lhs], validation[equation.rhs], strict=True)
    ]
    valid = sum(item.kind is ComparisonKind.EQUIVALENT for item in comparisons)
    invalid = sum(item.kind is ComparisonKind.INVALID_DOMAIN for item in comparisons)
    failed = sum(
        item.kind in {ComparisonKind.COUNTEREXAMPLE, ComparisonKind.ERROR}
        for item in comparisons
    )
    refuted_at = next(
        (
            position
            for position, item in enumerate(comparisons)
            if item.kind is ComparisonKind.COUNTEREXAMPLE
        ),
        None,
    )
    counterexample = None
    if equation.lhs in nondeterministic_terms or equation.rhs in nondeterministic_terms:
        verdict = Verdict.ERROR
    elif refuted_at is not None:
        verdict = Verdict.REFUTED
        counterexample = minimize_counterexample(
            worker, equation, validation_recipes[refuted_at]
        )
        counterexample["replay_id"] = f"axiom-{index:04d}-counterexample"
    elif failed:
        verdict = Verdict.ERROR
    elif valid >= minimum_valid_samples:
        verdict = Verdict.VALIDATED
    else:
        verdict = Verdict.CANDIDATE

    generator_ids = tuple(
        sorted(
            declaration.get("generator", "finite-values-v1")
            for declaration in manifest.types
        )
    )
    observer_ids = tuple(
        sorted(
            declaration.get("snapshot", "builtin-json-v1")
            for declaration in manifest.types
        )
    )
    return Finding(
        id=f"axiom-{index:04d}",
        equation=equation,
        verdict=verdict,
        discovery=SampleCounts(
            valid=candidate.valid_samples,
            invalid_domain=candidate.invalid_domain_samples,
            exceptions=candidate.invalid_domain_samples,
        ),
        validation=SampleCounts(
            valid=valid,
            invalid_domain=invalid,
            exceptions=invalid,
            failed=failed,
        ),
        generator_ids=generator_ids,
        observer_ids=observer_ids,
        exception_policy="common_domain",
        truncated=truncated,
        counterexample=counterexample,
    )


def _fingerprint_target(manifest: Manifest) -> str:
    digest = hashlib.sha256(manifest.source.read_bytes())
    for root in sorted(manifest.target.get("module_roots", [])):
        path = (manifest.source.parent / root).resolve()
        if not path.exists():
            continue
        files: Iterable[Path] = sorted(path.rglob("*.py")) if path.is_dir() else (path,)
        for file in files:
            digest.update(str(file.relative_to(path) if path.is_dir() else file.name).encode())
            digest.update(file.read_bytes())
    for entry in sorted(manifest.target.get("classpath", [])):
        path = (manifest.source.parent / entry).resolve()
        if not path.exists():
            continue
        files = sorted(path.rglob("*.class")) if path.is_dir() else (path,)
        for file in files:
            digest.update(str(file.relative_to(path) if path.is_dir() else file.name).encode())
            digest.update(file.read_bytes())
    jar = manifest.target.get("jar")
    if jar:
        path = (manifest.source.parent / jar).resolve()
        if path.is_file():
            digest.update(path.read_bytes())
    return "sha256:" + digest.hexdigest()
