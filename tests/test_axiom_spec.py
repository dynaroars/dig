from __future__ import annotations

import copy
import json
from pathlib import Path
import sys

import pytest

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "src"))

from axioms.spec import SpecValidationError, load_manifest, validate_manifest  # noqa: E402


EXAMPLES = REPO / "docs" / "axioms" / "examples"
SCHEMAS = REPO / "docs" / "axioms" / "schema"


def valid_manifest() -> dict:
    return {
        "schema_version": 1,
        "language": "python",
        "target": {"module_roots": ["fixtures"]},
        "types": [
            {
                "id": "item",
                "python_type": "builtins:int",
                "finite_values": [-1, 0, 1],
            }
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
            }
        ],
    }


def test_java_stack_manifest_is_valid_and_defaults_are_materialized():
    manifest = load_manifest(EXAMPLES / "java-stack.toml")
    assert manifest.language == "java"
    assert [operation["id"] for operation in manifest.operations] == ["push", "pop", "peek"]
    assert manifest.limits["validation_tests"] == 10
    operations = manifest.model_operations()
    assert operations[0].input_types == ("stack", "item")
    assert operations[0].mutates == {0}


@pytest.mark.parametrize(
    ("mutate", "field"),
    [
        (lambda data: data.update(schema_version=2), "schema_version"),
        (lambda data: data.update(surprise=True), "$"),
        (lambda data: data["target"].update(surprise=True), "target"),
        (lambda data: data["types"].append(copy.deepcopy(data["types"][0])), "types[1].id"),
        (lambda data: data["operations"][0].update(parameter_types=["missing"]), "parameter_types[0]"),
        (lambda data: data["operations"][0].update(mutates=[0]), "mutates"),
        (lambda data: data["operations"][0].pop("return_type"), "return_type"),
    ],
)
def test_invalid_manifests_report_the_field(mutate, field):
    data = valid_manifest()
    mutate(data)
    with pytest.raises(SpecValidationError, match=r"manifest\.toml:") as caught:
        validate_manifest(data, "manifest.toml")
    assert field in caught.value.field


def test_opaque_type_requires_observable_equality():
    data = valid_manifest()
    data["types"][0]["opaque"] = True
    with pytest.raises(SpecValidationError) as caught:
        validate_manifest(data, "manifest.toml")
    assert caught.value.field == "types[0]"
    assert "snapshot or comparator" in caught.value.detail


def test_opaque_python_type_also_requires_recipe_constructor():
    data = valid_manifest()
    data["types"][0].update(opaque=True, snapshot="fixtures:snapshot")
    with pytest.raises(SpecValidationError) as caught:
        validate_manifest(data, "manifest.toml")
    assert caught.value.field == "types[0]"
    assert "from_recipe" in caught.value.detail


def test_result_example_uses_type_correct_mutation_projection():
    result = json.loads((EXAMPLES / "java-stack-result.json").read_text())
    lhs = result["findings"][0]["equation"]["lhs"]
    push = lhs["children"][0]
    assert lhs["projection"] == {"kind": "return"}
    assert push["projection"] == {"kind": "post_state", "input_index": 0}
    assert push["type_id"] == "stack"


def test_json_schemas_parse_and_all_local_references_resolve():
    for path in sorted(SCHEMAS.glob("*.schema.json")):
        schema = json.loads(path.read_text())
        assert schema["$schema"].endswith("2020-12/schema")

        def visit(value):
            if isinstance(value, dict):
                reference = value.get("$ref")
                if isinstance(reference, str) and reference.startswith("#/$defs/"):
                    assert reference.removeprefix("#/$defs/") in schema["$defs"]
                for child in value.values():
                    visit(child)
            elif isinstance(value, list):
                for child in value:
                    visit(child)

        visit(schema)
