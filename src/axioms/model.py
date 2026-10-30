"""Immutable language-neutral model for algebraic axiom inference."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
import json
import math
import re
from typing import Any, Iterable, Mapping, TypeAlias


_ID = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")


class ModelValidationError(ValueError):
    """Raised when a model object violates the language-neutral contract."""


def _check_id(value: str, field: str) -> None:
    if not isinstance(value, str) or len(value) > 128 or not _ID.fullmatch(value):
        raise ModelValidationError(
            f"{field} must match [A-Za-z][A-Za-z0-9_.-]* and be at most 128 characters"
        )


def _check_encoded(value: Any, path: str = "value") -> None:
    """Accept deterministic JSON values and reject ambiguous/nonportable values."""

    if value is None or isinstance(value, (bool, str, int)):
        return
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ModelValidationError(f"{path} contains a non-finite float")
        return
    if isinstance(value, (list, tuple)):
        for index, child in enumerate(value):
            _check_encoded(child, f"{path}[{index}]")
        return
    if isinstance(value, Mapping):
        for key, child in value.items():
            if not isinstance(key, str):
                raise ModelValidationError(f"{path} contains a non-string object key")
            _check_encoded(child, f"{path}.{key}")
        return
    raise ModelValidationError(f"{path} contains unsupported value {type(value).__name__}")


class OperationKind(StrEnum):
    CONSTRUCTOR = "constructor"
    INSTANCE_METHOD = "instance_method"
    STATIC_METHOD = "static_method"
    CLASS_METHOD = "class_method"
    FUNCTION = "function"


class InputMode(StrEnum):
    OWNED = "owned"
    SHARED_BORROW = "shared_borrow"
    MUTABLE_BORROW = "mutable_borrow"


class ExceptionPolicy(StrEnum):
    COMMON_DOMAIN = "common_domain"
    SAME_EXCEPTION = "same_exception"


@dataclass(frozen=True, slots=True, order=True)
class TypeDef:
    id: str

    def __post_init__(self) -> None:
        _check_id(self.id, "type id")


@dataclass(frozen=True, slots=True)
class Operation:
    id: str
    kind: OperationKind
    parameter_types: tuple[str, ...]
    return_type: str | None
    mutates: frozenset[int] = frozenset()
    receiver_type: str | None = None
    parameter_modes: tuple[InputMode, ...] = ()
    receiver_mode: InputMode | None = None
    pure: bool = False
    commutative: bool = False
    exception_policy: ExceptionPolicy = ExceptionPolicy.COMMON_DOMAIN
    cost: int = 1

    def __post_init__(self) -> None:
        _check_id(self.id, "operation id")
        for index, type_id in enumerate(self.parameter_types):
            _check_id(type_id, f"parameter_types[{index}]")
        if self.return_type is not None:
            _check_id(self.return_type, "return_type")
        if self.kind is OperationKind.INSTANCE_METHOD:
            if self.receiver_type is None:
                raise ModelValidationError("instance methods require receiver_type")
            _check_id(self.receiver_type, "receiver_type")
        elif self.receiver_type is not None:
            raise ModelValidationError("receiver_type is only valid for instance methods")
        if type(self.cost) is not int or self.cost < 1:
            raise ModelValidationError("operation cost must be positive")
        if self.parameter_modes and len(self.parameter_modes) != len(self.parameter_types):
            raise ModelValidationError("parameter_modes must match parameter_types length")
        if self.receiver_mode is not None and self.receiver_type is None:
            raise ModelValidationError("receiver_mode requires receiver_type")
        if self.pure and self.mutates:
            raise ModelValidationError("a pure operation cannot declare mutations")
        if any(
            type(index) is not int or index < 0 or index >= len(self.input_types)
            for index in self.mutates
        ):
            raise ModelValidationError("mutation index is outside the logical inputs")
        if self.commutative:
            if self.receiver_type is not None:
                raise ModelValidationError("instance methods cannot be declared commutative")
            if len(self.parameter_types) < 2 or len(set(self.parameter_types)) != 1:
                raise ModelValidationError(
                    "commutative operations require at least two same-typed parameters"
                )

    @property
    def input_types(self) -> tuple[str, ...]:
        if self.receiver_type is None:
            return self.parameter_types
        return (self.receiver_type, *self.parameter_types)

    @property
    def input_modes(self) -> tuple[InputMode, ...]:
        parameter_modes = self.parameter_modes or (InputMode.OWNED,) * len(self.parameter_types)
        if self.receiver_type is None:
            return parameter_modes
        return (self.receiver_mode or InputMode.OWNED, *parameter_modes)


@dataclass(frozen=True, slots=True)
class ReturnProjection:
    kind: str = "return"


@dataclass(frozen=True, slots=True)
class PostStateProjection:
    input_index: int
    kind: str = "post_state"

    def __post_init__(self) -> None:
        if type(self.input_index) is not int or self.input_index < 0:
            raise ModelValidationError("post-state input index must be non-negative")


Projection: TypeAlias = ReturnProjection | PostStateProjection


@dataclass(frozen=True, slots=True)
class Variable:
    type_id: str
    index: int

    def __post_init__(self) -> None:
        _check_id(self.type_id, "variable type_id")
        if type(self.index) is not int or self.index < 0:
            raise ModelValidationError("variable index must be non-negative")


@dataclass(frozen=True, slots=True)
class Constant:
    type_id: str
    value: Any

    def __post_init__(self) -> None:
        _check_id(self.type_id, "constant type_id")
        _check_encoded(self.value)
        # Store list/object values in an immutable, canonical representation.
        object.__setattr__(self, "value", freeze_encoded_value(self.value))


@dataclass(frozen=True, slots=True)
class Call:
    operation_id: str
    projection: Projection
    type_id: str
    children: tuple[Term, ...]

    def __post_init__(self) -> None:
        _check_id(self.operation_id, "call operation_id")
        _check_id(self.type_id, "call type_id")


Term: TypeAlias = Variable | Constant | Call


@dataclass(frozen=True, slots=True)
class Equation:
    lhs: Term
    rhs: Term

    def __post_init__(self) -> None:
        if self.lhs.type_id != self.rhs.type_id:
            raise ModelValidationError("equation sides must have the same type")


@dataclass(frozen=True, slots=True)
class _FrozenList:
    items: tuple[Any, ...]


@dataclass(frozen=True, slots=True)
class _FrozenObject:
    items: tuple[tuple[str, Any], ...]


def freeze_encoded_value(value: Any) -> Any:
    if value is None or isinstance(value, (bool, str, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ModelValidationError("encoded value contains a non-finite float")
        return value
    if isinstance(value, list):
        return _FrozenList(tuple(freeze_encoded_value(child) for child in value))
    if isinstance(value, tuple):
        return _FrozenList(tuple(freeze_encoded_value(child) for child in value))
    if isinstance(value, Mapping):
        return _FrozenObject(
            tuple(sorted((key, freeze_encoded_value(child)) for key, child in value.items()))
        )
    raise ModelValidationError(f"encoded value contains unsupported {type(value).__name__}")


def thaw_encoded_value(value: Any) -> Any:
    if isinstance(value, _FrozenList):
        return [thaw_encoded_value(child) for child in value.items]
    if isinstance(value, _FrozenObject):
        return {key: thaw_encoded_value(child) for key, child in value.items}
    return value


def projected_type(operation: Operation, projection: Projection) -> str:
    if isinstance(projection, ReturnProjection):
        if operation.return_type is None:
            raise ModelValidationError(f"operation {operation.id!r} has no return projection")
        return operation.return_type
    if projection.input_index not in operation.mutates:
        raise ModelValidationError(
            f"operation {operation.id!r} does not mutate input {projection.input_index}"
        )
    return operation.input_types[projection.input_index]


def make_call(
    operation: Operation, children: Iterable[Term], projection: Projection
) -> Call:
    """Construct a type-checked call and normalize commutative children."""

    child_tuple = tuple(children)
    if len(child_tuple) != len(operation.input_types):
        raise ModelValidationError(
            f"operation {operation.id!r} expects {len(operation.input_types)} inputs, "
            f"got {len(child_tuple)}"
        )
    actual = tuple(child.type_id for child in child_tuple)
    if actual != operation.input_types:
        raise ModelValidationError(
            f"operation {operation.id!r} expects {operation.input_types}, got {actual}"
        )
    if operation.commutative:
        child_tuple = tuple(sorted(child_tuple, key=term_order_key))
    return Call(operation.id, projection, projected_type(operation, projection), child_tuple)


def term_to_data(term: Term) -> dict[str, Any]:
    if isinstance(term, Variable):
        return {"kind": "variable", "type_id": term.type_id, "index": term.index}
    if isinstance(term, Constant):
        return {
            "kind": "constant",
            "type_id": term.type_id,
            "value": thaw_encoded_value(term.value),
        }
    if isinstance(term.projection, ReturnProjection):
        projection = {"kind": "return"}
    else:
        projection = {"kind": "post_state", "input_index": term.projection.input_index}
    return {
        "kind": "call",
        "operation_id": term.operation_id,
        "projection": projection,
        "type_id": term.type_id,
        "children": [term_to_data(child) for child in term.children],
    }


def term_from_data(data: Mapping[str, Any], operations: Mapping[str, Operation]) -> Term:
    """Decode and type-check a term from its protocol representation."""

    kind = data.get("kind")
    if kind == "variable":
        return Variable(data.get("type_id"), data.get("index"))
    if kind == "constant":
        if "value" not in data:
            raise ModelValidationError("constant term is missing value")
        return Constant(data.get("type_id"), data["value"])
    if kind != "call":
        raise ModelValidationError(f"unsupported term kind {kind!r}")
    operation_id = data.get("operation_id")
    try:
        operation = operations[operation_id]
    except (KeyError, TypeError) as exc:
        raise ModelValidationError(f"unknown operation {operation_id!r}") from exc
    raw_projection = data.get("projection")
    if not isinstance(raw_projection, Mapping):
        raise ModelValidationError("call projection must be an object")
    projection_kind = raw_projection.get("kind")
    if projection_kind == "return":
        projection: Projection = ReturnProjection()
    elif projection_kind == "post_state":
        index = raw_projection.get("input_index")
        if type(index) is not int:
            raise ModelValidationError("post-state projection requires integer input_index")
        projection = PostStateProjection(index)
    else:
        raise ModelValidationError(f"unsupported projection {projection_kind!r}")
    raw_children = data.get("children")
    if not isinstance(raw_children, list):
        raise ModelValidationError("call children must be an array")
    call = make_call(
        operation,
        (term_from_data(child, operations) for child in raw_children),
        projection,
    )
    if data.get("type_id") != call.type_id:
        raise ModelValidationError(
            f"serialized call type {data.get('type_id')!r} does not match {call.type_id!r}"
        )
    return call


def equation_to_data(equation: Equation) -> dict[str, Any]:
    return {"lhs": term_to_data(equation.lhs), "rhs": term_to_data(equation.rhs)}


def equation_from_data(
    data: Mapping[str, Any], operations: Mapping[str, Operation]
) -> Equation:
    if not isinstance(data.get("lhs"), Mapping) or not isinstance(data.get("rhs"), Mapping):
        raise ModelValidationError("equation requires object-valued lhs and rhs")
    return Equation(
        term_from_data(data["lhs"], operations),
        term_from_data(data["rhs"], operations),
    )


def canonical_json(value: Any) -> str:
    """Return the stable JSON spelling used for ordering and fingerprints."""

    if isinstance(value, (Variable, Constant, Call)):
        value = term_to_data(value)
    elif isinstance(value, Equation):
        value = equation_to_data(value)
    _check_encoded(value)
    return json.dumps(value, ensure_ascii=False, allow_nan=False, sort_keys=True, separators=(",", ":"))


def term_cost(term: Term, operations: Mapping[str, Operation]) -> int:
    if not isinstance(term, Call):
        return 0
    try:
        operation = operations[term.operation_id]
    except KeyError as exc:
        raise ModelValidationError(f"unknown operation {term.operation_id!r}") from exc
    return operation.cost + sum(term_cost(child, operations) for child in term.children)


def term_order_key(term: Term) -> tuple[int, int, str, str]:
    """A stable structural order that prefers simpler terms."""

    def counts(node: Term) -> tuple[int, int]:
        if not isinstance(node, Call):
            return 0, 1
        child_counts = [counts(child) for child in node.children]
        return 1 + sum(item[0] for item in child_counts), 1 + sum(
            item[1] for item in child_counts
        )

    calls, nodes = counts(term)
    return calls, nodes, term.type_id, canonical_json(term)


def rename_variables(terms: Iterable[Term]) -> tuple[Term, ...]:
    """Rename variables by first occurrence, independently for each type."""

    assigned: dict[tuple[str, int], int] = {}
    next_index: dict[str, int] = {}

    def rename(term: Term) -> Term:
        if isinstance(term, Variable):
            key = (term.type_id, term.index)
            if key not in assigned:
                assigned[key] = next_index.get(term.type_id, 0)
                next_index[term.type_id] = assigned[key] + 1
            return Variable(term.type_id, assigned[key])
        if isinstance(term, Constant):
            return term
        return Call(
            term.operation_id,
            term.projection,
            term.type_id,
            tuple(rename(child) for child in term.children),
        )

    return tuple(rename(term) for term in terms)


def canonical_equation(lhs: Term, rhs: Term) -> Equation:
    """Normalize symmetry and variable names together."""

    if lhs.type_id != rhs.type_id:
        raise ModelValidationError("equation sides must have the same type")
    forward = rename_variables((lhs, rhs))
    reverse = rename_variables((rhs, lhs))
    selected = min((forward, reverse), key=lambda pair: canonical_json({
        "lhs": term_to_data(pair[0]), "rhs": term_to_data(pair[1])
    }))
    return Equation(*selected)


def format_term(term: Term) -> str:
    if isinstance(term, Variable):
        return f"{term.type_id}_{term.index}"
    if isinstance(term, Constant):
        return canonical_json(thaw_encoded_value(term.value))
    arguments = ", ".join(format_term(child) for child in term.children)
    call = f"{term.operation_id}({arguments})"
    if isinstance(term.projection, PostStateProjection):
        return f"post_state[{term.projection.input_index}]({call})"
    return call


def format_equation(equation: Equation) -> str:
    return f"{format_term(equation.lhs)} == {format_term(equation.rhs)}"
