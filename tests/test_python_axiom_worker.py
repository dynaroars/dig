from __future__ import annotations

import json
from pathlib import Path
import sys

import pytest

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
sys.path.insert(0, str(SRC))

from axioms.workers.python_worker import PythonWorker  # noqa: E402


MANIFEST = REPO / "docs" / "axioms" / "examples" / "python-stack.toml"
STACK_LAW = json.loads(
    (REPO / "docs" / "axioms" / "examples" / "stack-law-v1.json").read_text()
)


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


def test_worker_evaluates_both_sides_in_fresh_equivalent_worlds():
    cases = [
        {
            "case_id": side,
            "recipe": recipe(),
            "term": STACK_LAW[side],
            "observe_roots": ["s"],
        }
        for side in ("lhs", "rhs")
    ]
    with PythonWorker(MANIFEST) as worker:
        results = worker.evaluate_batch("stack-law", cases)

    lhs, rhs = (result["outcome"] for result in results)
    assert lhs["status"] == rhs["status"] == "returned"
    assert lhs["return_value"] == rhs["return_value"] == 3
    assert lhs["observations_by_root"] == rhs["observations_by_root"]
    assert lhs["observations_by_root"]["s"]["value"] == [1, 2]


def test_worker_reports_target_exception_as_data():
    pop = STACK_LAW["lhs"]
    # Remove the nested push, leaving pop(stack_0).
    pop = {**pop, "children": [STACK_LAW["lhs"]["children"][0]["children"][0]]}
    case = {
        "case_id": "empty-pop",
        "recipe": recipe(values=()),
        "term": pop,
        "observe_roots": ["s"],
    }
    with PythonWorker(MANIFEST) as worker:
        outcome = worker.evaluate_batch("exception", [case])[0]["outcome"]
    assert outcome["status"] == "threw"
    assert outcome["exception"]["class"] == "builtins.IndexError"


def test_worker_timeout_kills_the_process(tmp_path):
    manifest = tmp_path / "hang.toml"
    manifest.write_text(
        f'''schema_version = 1
language = "python"

[target]
module_roots = ["{(REPO / 'examples' / 'axioms').as_posix()}"]

[[types]]
id = "item"
python_type = "builtins:int"
finite_values = [0]

[[operations]]
id = "hang"
binding = "python_stack:hang"
kind = "function"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
'''
    )
    term = {
        "kind": "call",
        "operation_id": "hang",
        "projection": {"kind": "return"},
        "type_id": "item",
        "children": [{"kind": "variable", "type_id": "item", "index": 0}],
    }
    case = {
        "case_id": "hang",
        "recipe": {
            "recipe_id": "hang",
            "roots": [{"id": "x", "type_id": "item", "value": 0}],
            "variables": [{"type_id": "item", "index": 0, "root_id": "x"}],
        },
        "term": term,
    }
    worker = PythonWorker(manifest, timeout=0.1)
    worker.start()
    with pytest.raises(TimeoutError):
        worker.evaluate_batch("hang", [case])
    assert worker.process is None


def test_worker_recycles_after_configured_batch_count():
    case = {
        "case_id": "item",
        "recipe": recipe(),
        "term": STACK_LAW["rhs"],
    }
    with PythonWorker(MANIFEST, max_batches=1) as worker:
        assert worker.process is not None
        first_pid = worker.process.pid
        worker.evaluate_batch("first", [case])
        worker.evaluate_batch("second", [case])
        assert worker.process is not None
        assert worker.process.pid != first_pid


def test_declared_pure_operation_that_mutates_is_an_error(tmp_path):
    manifest = tmp_path / "impure.toml"
    manifest.write_text(
        f'''schema_version = 1
language = "python"
[target]
module_roots = ["{(REPO / 'examples' / 'axioms').as_posix()}"]
[[types]]
id = "items"
python_type = "builtins:list"
finite_values = [[]]
[[types]]
id = "item"
python_type = "builtins:int"
finite_values = [0]
[[operations]]
id = "impure_length"
binding = "python_stack:impure_length"
kind = "function"
parameter_types = ["items"]
return_type = "item"
mutates = []
pure = true
'''
    )
    case = {
        "case_id": "impure",
        "recipe": {
            "recipe_id": "impure",
            "roots": [{"id": "xs", "type_id": "items", "value": []}],
            "variables": [{"type_id": "items", "index": 0, "root_id": "xs"}],
        },
        "term": {
            "kind": "call",
            "operation_id": "impure_length",
            "projection": {"kind": "return"},
            "type_id": "item",
            "children": [{"kind": "variable", "type_id": "items", "index": 0}],
        },
    }
    with PythonWorker(manifest) as worker:
        outcome = worker.evaluate_batch("impure", [case])[0]["outcome"]
    assert outcome["status"] == "protocol_error"
    assert "mutated an input" in outcome["detail"]


def test_static_class_alias_and_bounded_output_support(tmp_path):
    manifest = tmp_path / "advanced.toml"
    manifest.write_text(
        f'''schema_version = 1
language = "python"
[target]
module_roots = ["{(REPO / 'examples' / 'axioms').as_posix()}"]
[[types]]
id = "item"
python_type = "builtins:int"
finite_values = [0, 1]
[[types]]
id = "items"
python_type = "builtins:list"
finite_values = [[], [0]]
[[types]]
id = "boolean"
python_type = "builtins:bool"
finite_values = [false, true]
[[operations]]
id = "double"
binding = "python_stack:Utility.double"
kind = "static_method"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
[[operations]]
id = "plus_offset"
binding = "python_stack:Utility.plus_offset"
kind = "class_method"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
[[operations]]
id = "same_object"
binding = "python_stack:same_object"
kind = "function"
parameter_types = ["items", "items"]
return_type = "boolean"
mutates = []
pure = true
[[operations]]
id = "noisy"
binding = "python_stack:noisy"
kind = "function"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
[limits]
output_limit_bytes = 64
'''
    )
    item = {"kind": "variable", "type_id": "item", "index": 0}
    cases = [
        {
            "case_id": operation,
            "recipe": {
                "recipe_id": operation,
                "roots": [{"id": "i", "type_id": "item", "value": 2}],
                "variables": [{"type_id": "item", "index": 0, "root_id": "i"}],
            },
            "term": {
                "kind": "call",
                "operation_id": operation,
                "projection": {"kind": "return"},
                "type_id": "item",
                "children": [item],
            },
        }
        for operation in ("double", "plus_offset", "noisy")
    ]
    same_term = {
        "kind": "call",
        "operation_id": "same_object",
        "projection": {"kind": "return"},
        "type_id": "boolean",
        "children": [
            {"kind": "variable", "type_id": "items", "index": 0},
            {"kind": "variable", "type_id": "items", "index": 1},
        ],
    }
    cases.append(
        {
            "case_id": "aliased",
            "recipe": {
                "recipe_id": "aliased",
                "roots": [{"id": "xs", "type_id": "items", "value": []}],
                "variables": [
                    {"type_id": "items", "index": 0, "root_id": "xs"},
                    {"type_id": "items", "index": 1, "root_id": "xs"},
                ],
            },
            "term": same_term,
        }
    )
    with PythonWorker(manifest) as worker:
        outcomes = {
            result["case_id"]: result["outcome"]
            for result in worker.evaluate_batch("advanced", cases)
        }
    assert outcomes["double"]["return_value"] == 4
    assert outcomes["plus_offset"]["return_value"] == 3
    assert outcomes["aliased"]["return_value"] is True
    assert outcomes["noisy"]["stdout"]["bytes"] > 10_000
    assert outcomes["noisy"]["stdout"]["truncated"] is True
    assert "prefix" not in outcomes["noisy"]["stdout"]


def test_user_recipe_generator_is_seeded_isolated_and_replayable(tmp_path):
    manifest = tmp_path / "generator.toml"
    manifest.write_text(
        f'''schema_version = 1
language = "python"
[target]
module_roots = ["{(REPO / 'examples' / 'axioms').as_posix()}"]
[[types]]
id = "item"
python_type = "builtins:int"
generator = "python_stack:integer_recipes"
[[operations]]
id = "identity"
binding = "python_stack:Utility.plus_offset"
kind = "static_method"
parameter_types = ["item"]
return_type = "item"
mutates = []
pure = true
'''
    )
    with PythonWorker(manifest) as worker:
        first = worker.generate_values("item", seed=9, count=8)
        second = worker.generate_values("item", seed=9, count=8)
        different = worker.generate_values("item", seed=10, count=8)
    assert first == second
    assert first[:5] == [0, 1, -1, 2**31 - 1, -(2**31)]
    assert first != different
