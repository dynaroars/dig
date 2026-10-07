from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


REPO = Path(__file__).resolve().parent.parent
MANIFEST = REPO / "docs" / "axioms" / "examples" / "python-stack.toml"
sys.path.insert(0, str(REPO / "src"))

from axioms.model import Equation, ReturnProjection, Variable, equation_to_data, make_call  # noqa: E402
from axioms.spec import load_manifest  # noqa: E402


def test_axiom_cli_writes_stable_json_without_entering_numerical_pipeline(tmp_path):
    output = tmp_path / "result.json"
    completed = subprocess.run(
        [
            sys.executable,
            "-O",
            str(REPO / "src" / "dig.py"),
            "--axioms",
            str(MANIFEST),
            "--seed",
            "42",
            "--json-output",
            str(output),
        ],
        cwd=REPO,
        check=True,
        capture_output=True,
        text=True,
    )
    data = json.loads(output.read_text())
    assert data["analysis_kind"] == "axioms"
    assert data["language"] == "python"
    assert data["seeds"]["root"] == 42
    assert "VALIDATED" in completed.stdout
    assert "pop(post_state[0](push(stack_0, item_0))) == item_0" in completed.stdout


def test_numerical_cli_still_requires_positional_input():
    completed = subprocess.run(
        [sys.executable, str(REPO / "src" / "dig.py")],
        cwd=REPO,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 2
    assert "a positional input or --axioms MANIFEST is required" in completed.stderr


def test_cli_replays_counterexample_from_result_document(tmp_path):
    manifest = load_manifest(MANIFEST)
    operations = {operation.id: operation for operation in manifest.model_operations()}
    stack = Variable("stack", 0)
    equation = Equation(
        make_call(operations["peek"], (stack,), ReturnProjection()),
        make_call(operations["pop"], (stack,), ReturnProjection()),
    )
    recipe = {
        "recipe_id": "minimal",
        "roots": [{"id": "r0", "type_id": "stack", "value": [0]}],
        "variables": [{"type_id": "stack", "index": 0, "root_id": "r0"}],
    }
    result = tmp_path / "refuted.json"
    result.write_text(
        json.dumps(
            {
                "findings": [
                    {
                        "id": "axiom-refuted",
                        "equation": equation_to_data(equation),
                        "evidence": {"counterexample": {"recipe": recipe}},
                    }
                ]
            }
        )
    )
    completed = subprocess.run(
        [
            sys.executable,
            str(REPO / "src" / "dig.py"),
            "--axioms",
            str(MANIFEST),
            "--replay-counterexample",
            str(result),
        ],
        cwd=REPO,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "axiom-refuted: counterexample" in completed.stdout
    assert "observed post-state differs" in completed.stdout


def test_cli_finite_verifier_promotes_only_with_scoped_proof(tmp_path):
    output = tmp_path / "proved.json"
    completed = subprocess.run(
        [
            sys.executable,
            str(REPO / "src" / "dig.py"),
            "--axioms",
            str(MANIFEST),
            "--verifier",
            "finite",
            "--json-output",
            str(output),
        ],
        cwd=REPO,
        check=True,
        capture_output=True,
        text=True,
    )
    data = json.loads(output.read_text())
    proved = [finding for finding in data["findings"] if finding["verdict"] == "PROVED"]
    assert proved
    assert all(
        finding["evidence"]["proof"]["scope"] == "finite-domain/common-defined-domain"
        for finding in proved
    )
    assert "proof: dig-finite-domain 1" in completed.stdout
