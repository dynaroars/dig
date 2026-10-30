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

from axioms.aliases import alias_patterns  # noqa: E402
from axioms.enumerate import enumerate_terms  # noqa: E402
from axioms.model import (  # noqa: E402
    Constant,
    InputMode,
    ModelValidationError,
    Operation,
    OperationKind,
    PostStateProjection,
    ReturnProjection,
    Variable,
    canonical_equation,
    canonical_json,
    equation_from_data,
    equation_to_data,
    make_call,
    term_cost,
    term_to_data,
)
from axioms.outcomes import (  # noqa: E402
    ComparisonKind,
    NormalizedException,
    Outcome,
    OutcomeStatus,
    compare_outcomes,
)


def stack_operations() -> tuple[Operation, ...]:
    return (
        Operation(
            "push",
            OperationKind.INSTANCE_METHOD,
            ("item",),
            "item",
            frozenset({0}),
            receiver_type="stack",
        ),
        Operation(
            "pop",
            OperationKind.INSTANCE_METHOD,
            (),
            "item",
            frozenset({0}),
            receiver_type="stack",
        ),
        Operation(
            "peek",
            OperationKind.INSTANCE_METHOD,
            (),
            "item",
            receiver_type="stack",
            pure=True,
        ),
    )


def test_mutable_post_state_projection_keeps_composition_typed():
    push, pop, _peek = stack_operations()
    stack = Variable("stack", 8)
    item = Variable("item", 4)
    pushed_stack = make_call(push, (stack, item), PostStateProjection(0))
    lhs = make_call(pop, (pushed_stack,), ReturnProjection())
    equation = canonical_equation(lhs, item)

    assert pushed_stack.type_id == "stack"
    assert lhs.type_id == "item"
    assert equation.lhs.type_id == equation.rhs.type_id == "item"
    canonical_lhs = make_call(
        pop,
        (
            make_call(
                push,
                (Variable("stack", 0), Variable("item", 0)),
                PostStateProjection(0),
            ),
        ),
        ReturnProjection(),
    )
    assert {equation.lhs, equation.rhs} == {
        canonical_lhs,
        Variable("item", 0),
    }
    operation_map = {operation.id: operation for operation in stack_operations()}
    assert equation_from_data(equation_to_data(equation), operation_map) == equation


def test_return_projection_cannot_be_used_for_void_operation():
    clear = Operation(
        "clear",
        OperationKind.INSTANCE_METHOD,
        (),
        None,
        frozenset({0}),
        receiver_type="stack",
    )
    with pytest.raises(ModelValidationError, match="no return projection"):
        make_call(clear, (Variable("stack", 0),), ReturnProjection())


def test_type_mismatch_is_rejected_before_evaluation():
    push = stack_operations()[0]
    with pytest.raises(ModelValidationError, match="expects"):
        make_call(
            push,
            (Variable("item", 0), Variable("item", 1)),
            PostStateProjection(0),
        )


def test_commutative_calls_are_canonicalized():
    add = Operation(
        "add",
        OperationKind.FUNCTION,
        ("item", "item"),
        "item",
        pure=True,
        commutative=True,
    )
    low = Variable("item", 0)
    high = Variable("item", 1)
    assert make_call(add, (high, low), ReturnProjection()) == make_call(
        add, (low, high), ReturnProjection()
    )


def test_constant_values_are_deeply_immutable_and_round_trip_to_json():
    source = {"values": [["a", 1]], "flags": [True, None]}
    constant = Constant("payload", source)
    source["values"][0].append(2)
    assert term_to_data(constant)["value"] == {
        "flags": [True, None],
        "values": [["a", 1]],
    }
    assert json.loads(canonical_json(constant))["kind"] == "constant"


def test_non_finite_constants_are_rejected():
    with pytest.raises(ModelValidationError, match="non-finite"):
        Constant("float", float("nan"))


def test_alias_patterns_are_canonical_and_type_safe():
    assert list(alias_patterns(("stack", "stack"))) == [(0, 0), (0, 1)]
    assert list(alias_patterns(("stack", "item", "stack"))) == [
        (0, 1, 0),
        (0, 1, 2),
    ]
    assert list(alias_patterns(("item", "item", "item"))) == [
        (0, 0, 0),
        (0, 0, 1),
        (0, 1, 0),
        (0, 1, 1),
        (0, 1, 2),
    ]


def test_typed_enumeration_counts_and_costs():
    operations = stack_operations()
    result = enumerate_terms(
        ("stack", "item"),
        operations,
        max_cost=1,
        variables_per_type=2,
    )
    # cost 0: two variables each. Cost 1 stack terms: push post-state (4),
    # pop post-state (2). Cost 1 item terms: push returns (4), pop (2), peek (2).
    assert len(result.terms_by_type["stack"]) == 8
    assert len(result.terms_by_type["item"]) == 10
    operation_map = {operation.id: operation for operation in operations}
    assert {term_cost(term, operation_map) for term in result.terms} == {0, 1}
    assert not result.truncated_types


def test_enumeration_cap_is_stable_and_reported():
    result = enumerate_terms(
        ("stack", "item"),
        stack_operations(),
        max_cost=2,
        variables_per_type=2,
        max_terms_per_type=3,
    )
    assert all(len(terms) == 3 for terms in result.terms_by_type.values())
    assert result.truncated_types == {"item", "stack"}


def test_canonical_equation_renames_and_orients_variables():
    lhs = Variable("item", 91)
    rhs = Variable("item", 27)
    first = canonical_equation(lhs, rhs)
    second = canonical_equation(rhs, lhs)
    assert first == second
    assert {first.lhs.index, first.rhs.index} == {0, 1}


def test_canonical_output_does_not_depend_on_hash_seed():
    code = """
from axioms.enumerate import enumerate_terms
from axioms.model import Operation, OperationKind, canonical_json
op = Operation('add', OperationKind.FUNCTION, ('item','item'), 'item', pure=True, commutative=True)
r = enumerate_terms({'item'}, {op}, max_cost=2, variables_per_type=2)
print('\\n'.join(canonical_json(t) for t in r.terms))
"""
    outputs = []
    for seed in ("1", "222"):
        environment = os.environ.copy()
        environment["PYTHONPATH"] = str(SRC)
        environment["PYTHONHASHSEED"] = seed
        outputs.append(
            subprocess.run(
                [sys.executable, "-c", code],
                check=True,
                capture_output=True,
                text=True,
                env=environment,
            ).stdout
        )
    assert outputs[0] == outputs[1]


def test_outcome_comparison_contract():
    returned = Outcome(
        OutcomeStatus.RETURNED,
        return_value=1,
        observations_by_root={"r0": [1, 2]},
    )
    changed = Outcome(
        OutcomeStatus.RETURNED,
        return_value=1,
        observations_by_root={"r0": [1]},
    )
    thrown = Outcome(
        OutcomeStatus.THREW,
        exception=NormalizedException("IndexError", "empty"),
    )
    assert compare_outcomes(returned, returned).kind is ComparisonKind.EQUIVALENT
    assert compare_outcomes(returned, changed).kind is ComparisonKind.COUNTEREXAMPLE
    assert compare_outcomes(thrown, thrown).kind is ComparisonKind.INVALID_DOMAIN
    assert compare_outcomes(
        thrown, thrown, same_exception_is_equivalent=True
    ).kind is ComparisonKind.EQUIVALENT
    assert compare_outcomes(thrown, returned).kind is ComparisonKind.COUNTEREXAMPLE
    assert compare_outcomes(
        Outcome(OutcomeStatus.TIMED_OUT), returned
    ).kind is ComparisonKind.ERROR


def test_outcome_detaches_and_freezes_nested_observations():
    observation = {"r0": [1, {"value": 2}]}
    outcome = Outcome(
        OutcomeStatus.RETURNED,
        return_value=[1, 2],
        observations_by_root=observation,
    )
    observation["r0"].append(3)
    assert hash(outcome)
    assert dict(outcome.observations_by_root) != observation


def test_rust_input_modes_are_preserved_in_language_neutral_operation():
    operation = Operation(
        "replace",
        OperationKind.INSTANCE_METHOD,
        ("item",),
        "item",
        frozenset({0}),
        receiver_type="slot",
        parameter_modes=(InputMode.OWNED,),
        receiver_mode=InputMode.MUTABLE_BORROW,
    )
    assert operation.input_modes == (InputMode.MUTABLE_BORROW, InputMode.OWNED)
