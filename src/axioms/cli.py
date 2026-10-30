"""CLI adapter kept separate from DIG's numerical argument machinery."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .engine import EngineConfig, run_java_finite, run_python_finite
from .render import render_json, render_text
from .model import equation_from_data
from .outcomes import ComparisonKind
from .replay import replay_equation
from .spec import load_manifest
from .workers.jvm_worker import JavaWorker
from .workers.python_worker import PythonWorker
from .verification import apply_finite_verifier, apply_smt_model_verifier


def run_from_args(args: Any) -> int:
    manifest_path = Path(args.axioms)
    manifest = load_manifest(manifest_path)
    if args.replay_counterexample:
        return _replay(args, manifest)
    config = EngineConfig(
        max_call_cost=args.max_call_cost or manifest.limits["max_call_cost"],
        variables_per_type=args.variables_per_type or manifest.limits["variables_per_type"],
        max_terms_per_type=args.max_terms_per_type or manifest.limits["max_terms_per_type"],
        discovery_tests=args.discovery_tests or manifest.limits["discovery_tests"],
        validation_tests=args.validation_tests or manifest.limits["validation_tests"],
        minimum_valid_samples=(
            args.minimum_valid_samples or manifest.limits["minimum_valid_samples"]
        ),
        root_seed=int(args.seed) if args.seed is not None else 42,
    )
    if manifest.language == "python":
        run = run_python_finite(
            manifest_path,
            config,
            python_executable=args.python_executable,
            worker_timeout=args.worker_timeout,
        )
    elif manifest.language == "java":
        run = run_java_finite(
            manifest_path,
            config,
            java_executable=args.java,
            javac_executable=args.javac,
        )
    else:
        raise ValueError(f"CLI execution is not implemented for {manifest.language}")
    if args.verifier == "finite":
        if manifest.language == "python":
            verifier_worker = PythonWorker(
                manifest.source,
                python_executable=args.python_executable,
                timeout=args.worker_timeout or manifest.limits["batch_timeout_ms"] / 1000,
            )
        else:
            verifier_worker = JavaWorker(
                manifest.source,
                java_executable=args.java,
                javac_executable=args.javac,
                timeout=args.worker_timeout or manifest.limits["batch_timeout_ms"] / 1000,
            )
        with verifier_worker:
            run = apply_finite_verifier(run, verifier_worker)
    elif args.verifier == "smt-model":
        run = apply_smt_model_verifier(run)
    text = render_text(run)
    if args.json_output == "-":
        print(render_json(run), end="")
    else:
        print(text, end="")
    if args.json_output and args.json_output != "-":
        Path(args.json_output).write_text(render_json(run))
    if args.writeresults:
        Path(args.writeresults).write_text(text)
    return 0


def _replay(args: Any, manifest) -> int:
    result = json.loads(Path(args.replay_counterexample).read_text())
    findings = result.get("findings", [])
    if args.finding:
        findings = [finding for finding in findings if finding.get("id") == args.finding]
    selected = next(
        (
            finding
            for finding in findings
            if finding.get("evidence", {}).get("counterexample") is not None
        ),
        None,
    )
    if selected is None:
        raise ValueError("result contains no matching counterexample")
    operations = {operation.id: operation for operation in manifest.model_operations()}
    equation = equation_from_data(selected["equation"], operations)
    counterexample = selected["evidence"]["counterexample"]
    if manifest.language == "python":
        worker = PythonWorker(
            manifest.source,
            python_executable=args.python_executable,
            timeout=args.worker_timeout or manifest.limits["batch_timeout_ms"] / 1000,
        )
    elif manifest.language == "java":
        worker = JavaWorker(
            manifest.source,
            java_executable=args.java,
            javac_executable=args.javac,
            timeout=args.worker_timeout or manifest.limits["batch_timeout_ms"] / 1000,
        )
    else:
        raise ValueError(f"replay is not implemented for {manifest.language}")
    with worker:
        comparison, lhs, rhs = replay_equation(
            worker, equation, counterexample["recipe"], f"replay-{selected['id']}"
        )
    print(f"{selected['id']}: {comparison.kind.value} ({comparison.detail})")
    print("lhs: " + json.dumps(lhs, sort_keys=True))
    print("rhs: " + json.dumps(rhs, sort_keys=True))
    return 0 if comparison.kind is ComparisonKind.COUNTEREXAMPLE else 1
