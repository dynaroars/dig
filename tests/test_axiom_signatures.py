from __future__ import annotations

import json
from pathlib import Path
import sys

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
sys.path.insert(0, str(SRC))

from axioms.enumerate import enumerate_terms  # noqa: E402
from axioms.engine import EngineConfig, run_python_finite  # noqa: E402
from axioms.evidence import Verdict  # noqa: E402
from axioms.model import Variable, canonical_json, term_to_data  # noqa: E402
from axioms.outcomes import (  # noqa: E402
    NormalizedException,
    Outcome,
    OutcomeStatus,
    outcome_from_data,
)
from axioms.recipes import finite_recipes  # noqa: E402
from axioms.signatures import (  # noqa: E402
    discover_by_pairwise_oracle,
    discover_by_signatures,
)
from axioms.spec import load_manifest  # noqa: E402
from axioms.workers.python_worker import PythonWorker  # noqa: E402


MANIFEST_PATH = REPO / "docs" / "axioms" / "examples" / "python-stack.toml"
STACK_LAW = json.loads(
    (REPO / "docs" / "axioms" / "examples" / "stack-law-v1.json").read_text()
)


def returned(value):
    return Outcome(OutcomeStatus.RETURNED, return_value=value)


def test_signature_grouping_matches_pairwise_oracle_for_equivalence_classes():
    a, b, c = (Variable("item", index) for index in range(3))
    observations = {
        a: [returned(0), returned(1)],
        b: [returned(0), returned(1)],
        c: [returned(0), returned(2)],
    }
    grouped = discover_by_signatures(observations, minimum_valid_samples=2)
    oracle = discover_by_pairwise_oracle(observations, minimum_valid_samples=2)
    assert tuple(candidate.equation for candidate in grouped.candidates) == oracle


def test_exception_only_signature_does_not_create_vacuous_candidate():
    exception = NormalizedException("builtins.IndexError", "empty")
    observations = {
        Variable("item", 0): [Outcome(OutcomeStatus.THREW, exception=exception)],
        Variable("item", 1): [Outcome(OutcomeStatus.THREW, exception=exception)],
    }
    result = discover_by_signatures(observations, minimum_valid_samples=1)
    assert not result.candidates
    assert result.insufficient_domain_pairs == 1


def test_finite_recipe_generation_covers_stack_boundaries_deterministically():
    manifest = load_manifest(MANIFEST_PATH)
    first = finite_recipes(manifest, {"stack": 1, "item": 1}, seed=7, limit=20)
    second = finite_recipes(manifest, {"item": 1, "stack": 1}, seed=7, limit=20)
    assert first == second
    assert len(first) == 20
    stack_values = {
        json.dumps(next(root["value"] for root in recipe["roots"] if root["type_id"] == "stack"))
        for recipe in first
    }
    assert stack_values == {"[]", "[0]", "[1, 2]", "[1, 1]"}


def test_python_stack_discovery_finds_the_golden_law():
    manifest = load_manifest(MANIFEST_PATH)
    operations = manifest.model_operations()
    terms = enumerate_terms(
        ("stack", "item"), operations, max_cost=2, variables_per_type=1
    ).terms
    recipes = finite_recipes(manifest, {"stack": 1, "item": 1}, seed=11, limit=20)
    cases = [
        {
            "case_id": f"t{term_index}-r{recipe_index}",
            "recipe": recipe,
            "term": term_to_data(term),
            "observe_roots": [root["id"] for root in recipe["roots"]],
        }
        for term_index, term in enumerate(terms)
        for recipe_index, recipe in enumerate(recipes)
    ]
    with PythonWorker(MANIFEST_PATH) as worker:
        raw_results = []
        for offset in range(0, len(cases), 100):
            raw_results.extend(
                worker.evaluate_batch(f"discovery-{offset // 100}", cases[offset : offset + 100])
            )
    observations = {
        term: tuple(
            outcome_from_data(raw_results[term_index * len(recipes) + recipe_index]["outcome"])
            for recipe_index in range(len(recipes))
        )
        for term_index, term in enumerate(terms)
    }
    result = discover_by_signatures(observations, minimum_valid_samples=20)
    expected = canonical_json(STACK_LAW)
    assert any(canonical_json(candidate.equation) == expected for candidate in result.candidates)


def test_engine_runs_independent_discovery_and_validation_deterministically():
    config = EngineConfig(
        max_call_cost=2,
        variables_per_type=1,
        discovery_tests=10,
        validation_tests=10,
        minimum_valid_samples=5,
        root_seed=42,
    )
    first = run_python_finite(MANIFEST_PATH, config)
    second = run_python_finite(MANIFEST_PATH, config)
    expected = canonical_json(STACK_LAW)
    golden = [
        finding
        for finding in first.findings
        if canonical_json(finding.equation) == expected
    ]
    assert len(golden) == 1
    assert golden[0].verdict is Verdict.VALIDATED
    assert golden[0].discovery.valid == 10
    assert golden[0].validation.valid == 10
    assert first.to_data() == second.to_data()
    assert set(first.seeds) == {"root", "discovery", "validation", "shrinking", "mutation"}


def test_engine_uses_isolated_user_generator_when_finite_values_are_absent(tmp_path):
    manifest_path = tmp_path / "generated.toml"
    manifest_path.write_text(
        f'''schema_version = 1
language = "python"
[target]
module_roots = ["{(REPO / 'examples' / 'axioms').as_posix()}"]
[[types]]
id = "item"
python_type = "builtins:int"
generator = "python_stack:integer_recipes"
[[operations]]
id = "negate"
binding = "operator:neg"
kind = "function"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
'''
    )
    run = run_python_finite(
        manifest_path,
        EngineConfig(
            max_call_cost=2,
            variables_per_type=1,
            discovery_tests=5,
            validation_tests=5,
            minimum_valid_samples=3,
            root_seed=71,
        ),
    )
    assert any(
        finding.verdict is Verdict.VALIDATED
        and "negate(negate(item_0))" in finding.to_data()["text"]
        for finding in run.findings
    )
