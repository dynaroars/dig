from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
sys.path.insert(0, str(SRC))

from axioms.outcomes import ComparisonKind, compare_outcomes, outcome_from_data  # noqa: E402
from axioms.engine import EngineConfig, run_java_finite, run_python_finite  # noqa: E402
from axioms.evidence import Verdict  # noqa: E402
from axioms.model import canonical_json  # noqa: E402
from axioms.workers.jvm_worker import JavaWorker  # noqa: E402
from axioms.workers.python_worker import PythonWorker  # noqa: E402


JAVA_MANIFEST = REPO / "docs" / "axioms" / "examples" / "java-stack.toml"
PYTHON_MANIFEST = REPO / "docs" / "axioms" / "examples" / "python-stack.toml"
STACK_LAW = json.loads(
    (REPO / "docs" / "axioms" / "examples" / "stack-law-v1.json").read_text()
)
UNPACKED_JAVAC = Path(
    "/tmp/dig-jdk25/usr/lib/jvm/java-25-openjdk-amd64/bin/javac"
)


def java_tooling():
    system_javac = next(
        (Path(path) / "javac" for path in os.environ.get("PATH", "").split(os.pathsep)
         if (Path(path) / "javac").is_file()),
        None,
    )
    if system_javac is not None:
        return str(system_javac), {}
    if UNPACKED_JAVAC.is_file():
        return str(UNPACKED_JAVAC), {
            "LD_LIBRARY_PATH": (
                "/usr/lib/jvm/java-25-openjdk-amd64/lib:"
                "/usr/lib/jvm/java-25-openjdk-amd64/lib/server"
            )
        }
    pytest.skip("a JDK compiler is required for JVM worker tests")


def recipe(values=(1, 2), item=3):
    return {
        "recipe_id": "case-1",
        "roots": [
            {"id": "s", "type_id": "stack", "value": list(values)},
            {"id": "x", "type_id": "item", "value": item},
        ],
        "variables": [
            {"type_id": "stack", "index": 0, "root_id": "s"},
            {"type_id": "item", "index": 0, "root_id": "x"},
        ],
    }


def law_cases():
    return [
        {
            "case_id": side,
            "recipe": recipe(),
            "term": STACK_LAW[side],
            "observe_roots": ["s"],
        }
        for side in ("lhs", "rhs")
    ]


def test_jvm_stack_law_and_python_backend_have_equivalent_outcomes():
    javac, compiler_environment = java_tooling()
    with JavaWorker(
        JAVA_MANIFEST,
        javac_executable=javac,
        compiler_environment=compiler_environment,
    ) as java_worker:
        java_results = java_worker.evaluate_batch("stack-law", law_cases())
    with PythonWorker(PYTHON_MANIFEST) as python_worker:
        python_results = python_worker.evaluate_batch("stack-law", law_cases())

    for java_result, python_result in zip(java_results, python_results, strict=True):
        java_outcome = outcome_from_data(java_result["outcome"])
        python_outcome = outcome_from_data(python_result["outcome"])
        comparison = compare_outcomes(java_outcome, python_outcome)
        assert comparison.kind is ComparisonKind.EQUIVALENT, comparison.detail


def test_jvm_worker_reports_empty_pop_exception():
    javac, compiler_environment = java_tooling()
    pop = {**STACK_LAW["lhs"], "children": [STACK_LAW["lhs"]["children"][0]["children"][0]]}
    case = {
        "case_id": "empty-pop",
        "recipe": recipe(values=()),
        "term": pop,
        "observe_roots": ["s"],
    }
    with JavaWorker(
        JAVA_MANIFEST,
        javac_executable=javac,
        compiler_environment=compiler_environment,
    ) as worker:
        outcome = worker.evaluate_batch("exception", [case])[0]["outcome"]
    assert outcome["status"] == "threw"
    assert outcome["exception"]["class"] == "java.util.EmptyStackException"


def test_java_and_python_discovery_find_the_same_normalized_stack_law():
    javac, compiler_environment = java_tooling()
    config = EngineConfig(
        max_call_cost=2,
        variables_per_type=1,
        discovery_tests=10,
        validation_tests=10,
        minimum_valid_samples=5,
        root_seed=42,
    )
    java_run = run_java_finite(
        JAVA_MANIFEST,
        config,
        javac_executable=javac,
        compiler_environment=compiler_environment,
    )
    python_run = run_python_finite(PYTHON_MANIFEST, config)
    expected = canonical_json(STACK_LAW)
    for run in (java_run, python_run):
        matches = [
            finding
            for finding in run.findings
            if canonical_json(finding.equation) == expected
        ]
        assert len(matches) == 1
        assert matches[0].verdict is Verdict.VALIDATED


def test_jvm_resolves_overloads_and_compares_primitive_arrays_deeply(tmp_path):
    javac, compiler_environment = java_tooling()
    classes = tmp_path / "classes"
    classes.mkdir()
    source = (
        REPO
        / "jvm"
        / "axiom-runner"
        / "src"
        / "test"
        / "java"
        / "fixtures"
        / "Advanced.java"
    )
    subprocess.run(
        [javac, "-d", str(classes), str(source)],
        check=True,
        capture_output=True,
        text=True,
        env={**os.environ, **compiler_environment},
    )
    manifest = tmp_path / "advanced.toml"
    manifest.write_text(
        f'''schema_version = 1
language = "java"
[target]
classpath = ["{classes.as_posix()}"]
[[types]]
id = "item"
java_class = "java.lang.Integer"
finite_values = [1]
[[types]]
id = "text"
java_class = "java.lang.String"
finite_values = ["a"]
[[types]]
id = "items"
java_class = "int[]"
finite_values = [[1, 2, 3]]
[[operations]]
id = "overloaded_int"
binding = "fixtures.Advanced#overloaded(int)"
kind = "static_method"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
[[operations]]
id = "overloaded_text"
binding = "fixtures.Advanced#overloaded(java.lang.String)"
kind = "static_method"
parameter_types = ["text"]
return_type = "text"
mutates = []
pure = true
[[operations]]
id = "reverse"
binding = "fixtures.Advanced#reverse(int[])"
kind = "static_method"
parameter_types = ["items"]
return_type = "items"
mutates = []
pure = true
'''
    )
    roots = [
        {"id": "i", "type_id": "item", "value": 4},
        {"id": "s", "type_id": "text", "value": "ok"},
        {"id": "a", "type_id": "items", "value": [1, 2, 3]},
    ]
    variables = [
        {"type_id": "item", "index": 0, "root_id": "i"},
        {"type_id": "text", "index": 0, "root_id": "s"},
        {"type_id": "items", "index": 0, "root_id": "a"},
    ]
    cases = []
    for operation, type_id in (
        ("overloaded_int", "item"),
        ("overloaded_text", "text"),
        ("reverse", "items"),
    ):
        cases.append(
            {
                "case_id": operation,
                "recipe": {"recipe_id": operation, "roots": roots, "variables": variables},
                "term": {
                    "kind": "call",
                    "operation_id": operation,
                    "projection": {"kind": "return"},
                    "type_id": type_id,
                    "children": [{"kind": "variable", "type_id": type_id, "index": 0}],
                },
            }
        )
    with JavaWorker(
        manifest,
        javac_executable=javac,
        compiler_environment=compiler_environment,
    ) as worker:
        outcomes = {
            result["case_id"]: result["outcome"]
            for result in worker.evaluate_batch("advanced", cases)
        }
    assert outcomes["overloaded_int"]["return_value"] == 5
    assert outcomes["overloaded_text"]["return_value"] == "ok!"
    assert outcomes["reverse"]["return_value"] == [3, 2, 1]
