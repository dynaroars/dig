from __future__ import annotations

import json
from pathlib import Path
import sys

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
sys.path.insert(0, str(SRC))

from axioms.model import (  # noqa: E402
    Equation,
    PostStateProjection,
    ReturnProjection,
    Variable,
    make_call,
    term_from_data,
)
from axioms.spec import load_manifest  # noqa: E402
from axioms.verify import FiniteDomainVerifier, ProofStatus  # noqa: E402
from axioms.workers.python_worker import PythonWorker  # noqa: E402


MANIFEST_PATH = REPO / "docs" / "axioms" / "examples" / "python-stack.toml"
STACK_LAW = json.loads(
    (REPO / "docs" / "axioms" / "examples" / "stack-law-v1.json").read_text()
)


def test_finite_verifier_proves_stack_law_with_explicit_scope():
    manifest = load_manifest(MANIFEST_PATH)
    operations = {operation.id: operation for operation in manifest.model_operations()}
    equation = Equation(
        term_from_data(STACK_LAW["lhs"], operations),
        term_from_data(STACK_LAW["rhs"], operations),
    )
    with PythonWorker(MANIFEST_PATH) as worker:
        result = FiniteDomainVerifier().verify(worker, manifest, equation)
    assert result.status is ProofStatus.PROVED
    assert result.scope == "finite-domain/common-defined-domain"
    assert result.cases_checked == 20
    assert result.valid_cases == 20
    assert result.artifact_digest.startswith("sha256:")


def test_finite_verifier_refutes_equal_return_but_different_post_state():
    manifest = load_manifest(MANIFEST_PATH)
    operations = {operation.id: operation for operation in manifest.model_operations()}
    stack = Variable("stack", 0)
    peek = make_call(operations["peek"], (stack,), ReturnProjection())
    pop = make_call(operations["pop"], (stack,), ReturnProjection())
    equation = Equation(peek, pop)
    with PythonWorker(MANIFEST_PATH) as worker:
        result = FiniteDomainVerifier().verify(worker, manifest, equation)
    assert result.status is ProofStatus.REFUTED
    assert result.counterexample is not None


def test_finite_verifier_declines_missing_finite_domain():
    manifest = load_manifest(MANIFEST_PATH)
    operations = {operation.id: operation for operation in manifest.model_operations()}
    stack = Variable("stack", 0)
    pushed = make_call(
        operations["push"],
        (stack, Variable("item", 0)),
        PostStateProjection(0),
    )
    # The manifest is supported; removing the declaration's finite values makes
    # support fail without executing target code.
    stack_decl = dict(manifest.types[0])
    stack_decl.pop("finite_values")
    altered = type(manifest)(
        manifest.source,
        manifest.language,
        manifest.target,
        (stack_decl, *manifest.types[1:]),
        manifest.operations,
        manifest.limits,
        manifest.extensions,
    )
    supported, detail = FiniteDomainVerifier().supports(altered, Equation(pushed, stack))
    assert not supported
    assert "finite_values" in detail

