from __future__ import annotations

from pathlib import Path
import sys

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
sys.path.insert(0, str(SRC))

from axioms.model import (  # noqa: E402
    Operation,
    OperationKind,
    ReturnProjection,
    Variable,
    make_call,
)
from axioms.robustness import replay_is_deterministic  # noqa: E402
from axioms.replay import minimize_counterexample  # noqa: E402
from axioms.spec import load_manifest  # noqa: E402
from axioms.shrink import shrink_recipe, shrink_value  # noqa: E402
from axioms.workers.python_worker import PythonWorker  # noqa: E402

MANIFEST = REPO / "docs" / "axioms" / "examples" / "python-stack.toml"


def test_value_shrinking_moves_toward_boundaries_and_deletes_sequence_parts():
    assert list(shrink_value(10))[:3] == [0, 5, 2]
    sequence_moves = list(shrink_value([10, 20]))
    assert [] in sequence_moves
    assert [10] in sequence_moves
    assert [0, 20] in sequence_moves


def test_recipe_shrinking_can_simplify_alias_graph():
    recipe = {
        "recipe_id": "alias",
        "roots": [
            {"id": "r0", "type_id": "item", "value": 1},
            {"id": "r1", "type_id": "item", "value": 2},
        ],
        "variables": [
            {"type_id": "item", "index": 0, "root_id": "r0"},
            {"type_id": "item", "index": 1, "root_id": "r1"},
        ],
    }
    moves = list(shrink_recipe(recipe))
    assert any(
        len(move["roots"]) == 1
        and {variable["root_id"] for variable in move["variables"]} == {"r0"}
        for move in moves
    )


def test_replay_detects_nondeterministic_operation(tmp_path):
    manifest = tmp_path / "nondeterministic.toml"
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
id = "nondeterministic"
binding = "python_stack:nondeterministic"
kind = "function"
parameter_types = ["item"]
return_type = "item"
mutates = []
'''
    )
    operation = Operation(
        "nondeterministic",
        OperationKind.FUNCTION,
        ("item",),
        "item",
    )
    term = make_call(operation, (Variable("item", 0),), ReturnProjection())
    recipe = {
        "recipe_id": "nondeterministic",
        "roots": [{"id": "r0", "type_id": "item", "value": 0}],
        "variables": [{"type_id": "item", "index": 0, "root_id": "r0"}],
    }
    with PythonWorker(manifest) as worker:
        assert not replay_is_deterministic(worker, term, recipe, replays=3)


def test_counterexample_shrinking_preserves_refutation():
    manifest = load_manifest(MANIFEST)
    operations = {operation.id: operation for operation in manifest.model_operations()}
    stack = Variable("stack", 0)
    peek = make_call(operations["peek"], (stack,), ReturnProjection())
    pop = make_call(operations["pop"], (stack,), ReturnProjection())
    recipe = {
        "recipe_id": "large",
        "roots": [{"id": "r0", "type_id": "stack", "value": [10, 20, 30]}],
        "variables": [{"type_id": "stack", "index": 0, "root_id": "r0"}],
    }
    from axioms.model import Equation

    with PythonWorker(MANIFEST) as worker:
        counterexample = minimize_counterexample(worker, Equation(peek, pop), recipe)
    assert counterexample["recipe"]["roots"][0]["value"] == [0]
    assert counterexample["lhs_outcome"]["return_value"] == 0
    assert counterexample["rhs_outcome"]["return_value"] == 0
