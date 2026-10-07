from __future__ import annotations

from pathlib import Path
import sys

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "src"))

from axioms.model import Equation, ReturnProjection, Variable, make_call  # noqa: E402
from axioms.spec import validate_manifest  # noqa: E402
from axioms.verify import ProofStatus, SmtModelVerifier  # noqa: E402


EXTENSION = "org.dynaroars.dig.smt"


def modeled_manifest():
    return validate_manifest(
        {
            "schema_version": 1,
            "language": "python",
            "target": {"module_roots": ["fixtures"]},
            "types": [
                {"id": "item", "python_type": "builtins:int", "finite_values": [0]}
            ],
            "operations": [
                {
                    "id": "negate",
                    "binding": "operator:neg",
                    "kind": "function",
                    "parameter_types": ["item"],
                    "return_type": "item",
                    "mutates": [],
                    "pure": True,
                    "extensions": {
                        EXTENSION: {
                            "result": {
                                "kind": "neg",
                                "args": [{"kind": "arg", "index": 0}],
                            }
                        }
                    },
                }
            ],
            "extensions": {EXTENSION: {"type_sorts": {"item": "int"}}},
        },
        "modeled.toml",
    )


def test_smt_model_verifier_proves_only_model_scope():
    manifest = modeled_manifest()
    negate = manifest.model_operations()[0]
    item = Variable("item", 0)
    twice = make_call(
        negate,
        (make_call(negate, (item,), ReturnProjection()),),
        ReturnProjection(),
    )
    result = SmtModelVerifier().verify(manifest, Equation(twice, item))
    assert result.status is ProofStatus.PROVED
    assert result.scope == "model"
    assert "logical operation models" in result.assumptions[0]


def test_smt_model_verifier_returns_serializable_model_counterexample():
    manifest = modeled_manifest()
    negate = manifest.model_operations()[0]
    item = Variable("item", 0)
    negated = make_call(negate, (item,), ReturnProjection())
    result = SmtModelVerifier().verify(manifest, Equation(negated, item))
    assert result.status is ProofStatus.REFUTED
    assert result.scope == "model"
    assert result.counterexample is not None
    value = result.counterexample["recipe"]["roots"][0]["value"]
    assert value != 0

