"""Versioned axiom manifest loading and pre-execution validation.

This module intentionally does not import or inspect the target API. A malformed
manifest must fail before target-controlled code can run.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import tomllib
from typing import Any, Mapping

from .model import ExceptionPolicy, InputMode, Operation, OperationKind


_ID = re.compile(r"^[A-Za-z][A-Za-z0-9_.-]*$")
_LANGUAGES = frozenset({"python", "java", "rust"})
_KINDS = frozenset(
    {"constructor", "instance_method", "static_method", "class_method", "function"}
)
_MODES = frozenset({"owned", "shared_borrow", "mutable_borrow"})
_EXCEPTION_POLICIES = frozenset({"common_domain", "same_exception"})

_TOP_FIELDS = frozenset(
    {"schema_version", "language", "target", "types", "operations", "limits", "extensions"}
)
_TARGET_FIELDS = frozenset(
    {"module_roots", "classpath", "jar", "manifest_path", "package", "features"}
)
_TYPE_FIELDS = frozenset(
    {
        "id", "python_type", "java_class", "rust_type", "generator", "from_recipe",
        "snapshot", "comparator", "adapter", "finite_values", "opaque", "extensions",
    }
)
_OP_FIELDS = frozenset(
    {
        "id", "display_name", "binding", "kind", "receiver_type", "parameter_types",
        "parameter_modes", "receiver_mode", "return_type", "mutates", "pure",
        "commutative", "exception_policy", "precondition", "cost", "extensions",
    }
)
_LIMIT_DEFAULTS = {
    "max_call_cost": 3,
    "variables_per_type": 2,
    "max_terms_per_type": 1_000,
    "max_candidates": 10_000,
    "discovery_tests": 100,
    "validation_tests": 1_000,
    "minimum_valid_samples": 20,
    "case_timeout_ms": 1_000,
    "batch_timeout_ms": 30_000,
    "worker_memory_mib": 512,
    "output_limit_bytes": 65_536,
}


class SpecValidationError(ValueError):
    """A manifest error with a source path and dotted field location."""

    def __init__(self, source: Path, field: str, message: str) -> None:
        self.source = source
        self.field = field
        self.detail = message
        super().__init__(f"{source}:{field}: {message}")


@dataclass(frozen=True, slots=True)
class Manifest:
    """A validated schema-v1 manifest without imported target objects."""

    source: Path
    language: str
    target: Mapping[str, Any]
    types: tuple[Mapping[str, Any], ...]
    operations: tuple[Mapping[str, Any], ...]
    limits: Mapping[str, int]
    extensions: Mapping[str, Any]

    def model_operations(self) -> tuple[Operation, ...]:
        """Compile validated declarations into immutable core operations."""

        return tuple(
            Operation(
                id=declaration["id"],
                kind=OperationKind(declaration["kind"]),
                receiver_type=declaration.get("receiver_type"),
                parameter_types=tuple(declaration["parameter_types"]),
                return_type=declaration["return_type"],
                mutates=frozenset(declaration["mutates"]),
                parameter_modes=tuple(
                    InputMode(mode) for mode in declaration.get("parameter_modes", ())
                ),
                receiver_mode=(
                    InputMode(declaration["receiver_mode"])
                    if "receiver_mode" in declaration
                    else None
                ),
                pure=declaration.get("pure", False),
                commutative=declaration.get("commutative", False),
                exception_policy=ExceptionPolicy(
                    declaration.get("exception_policy", "common_domain")
                ),
                cost=declaration.get("cost", 1),
            )
            for declaration in self.operations
        )


def _fail(source: Path, field: str, message: str) -> None:
    raise SpecValidationError(source, field, message)


def _mapping(value: Any, source: Path, field: str) -> Mapping[str, Any]:
    if not isinstance(value, dict):
        _fail(source, field, "must be a table/object")
    return value


def _list(value: Any, source: Path, field: str) -> list[Any]:
    if not isinstance(value, list):
        _fail(source, field, "must be an array")
    return value


def _known_fields(
    value: Mapping[str, Any], allowed: frozenset[str], source: Path, field: str
) -> None:
    unknown = sorted(set(value) - allowed)
    if unknown:
        _fail(source, field, f"unknown field(s): {', '.join(unknown)}")


def _stable_id(value: Any, source: Path, field: str) -> str:
    if not isinstance(value, str) or len(value) > 128 or not _ID.fullmatch(value):
        _fail(source, field, "must be a stable ID matching [A-Za-z][A-Za-z0-9_.-]*")
    return value


def _extensions(value: Any, source: Path, field: str) -> Mapping[str, Any]:
    table = _mapping(value, source, field)
    for key in table:
        if "." not in key or any(not part for part in key.split(".")):
            _fail(source, f"{field}.{key}", "extension keys must use reverse-DNS notation")
    return table


def validate_manifest(data: Mapping[str, Any], source: Path | str = "<memory>") -> Manifest:
    """Validate decoded TOML without loading any target-controlled code."""

    source = Path(source)
    root = _mapping(data, source, "$")
    _known_fields(root, _TOP_FIELDS, source, "$")

    if root.get("schema_version") != 1:
        _fail(source, "schema_version", "unsupported schema version; expected 1")
    language = root.get("language")
    if language not in _LANGUAGES:
        _fail(source, "language", f"must be one of {sorted(_LANGUAGES)}")

    target = _mapping(root.get("target"), source, "target")
    _known_fields(target, _TARGET_FIELDS, source, "target")
    target_key = {"python": "module_roots", "java": "classpath", "rust": "manifest_path"}[language]
    if target_key not in target:
        _fail(source, f"target.{target_key}", f"is required for language {language}")
    target_value = target[target_key]
    if target_key in {"module_roots", "classpath"}:
        if not isinstance(target_value, list) or not target_value or any(
            not isinstance(item, str) or not item for item in target_value
        ):
            _fail(source, f"target.{target_key}", "must be a non-empty array of paths")
    elif not isinstance(target_value, str) or not target_value:
        _fail(source, f"target.{target_key}", "must be a non-empty path")

    raw_types = _list(root.get("types"), source, "types")
    if not raw_types:
        _fail(source, "types", "must contain at least one type")
    bindings = {"python": "python_type", "java": "java_class", "rust": "rust_type"}
    binding_key = bindings[language]
    type_ids: set[str] = set()
    types: list[Mapping[str, Any]] = []
    for index, raw_type in enumerate(raw_types):
        field = f"types[{index}]"
        declaration = _mapping(raw_type, source, field)
        _known_fields(declaration, _TYPE_FIELDS, source, field)
        if "id" not in declaration:
            _fail(source, f"{field}.id", "is required")
        type_id = _stable_id(declaration.get("id"), source, f"{field}.id")
        if type_id in type_ids:
            _fail(source, f"{field}.id", f"duplicate type ID {type_id!r}")
        type_ids.add(type_id)
        binding = declaration.get(binding_key)
        if not isinstance(binding, str) or not binding:
            _fail(source, f"{field}.{binding_key}", f"is required for language {language}")
        foreign_bindings = set(bindings.values()) - {binding_key}
        if foreign_bindings.intersection(declaration):
            _fail(source, field, "contains a binding for a different language")
        if declaration.get("opaque", False) and not (
            declaration.get("snapshot") or declaration.get("comparator")
        ):
            _fail(source, field, "opaque types require a snapshot or comparator")
        if declaration.get("opaque", False) and language == "python" and not declaration.get(
            "from_recipe"
        ):
            _fail(source, field, "opaque Python types require from_recipe")
        if "finite_values" in declaration and not declaration["finite_values"]:
            _fail(source, f"{field}.finite_values", "must not be empty")
        if "extensions" in declaration:
            _extensions(declaration["extensions"], source, f"{field}.extensions")
        types.append(declaration)

    raw_operations = _list(root.get("operations"), source, "operations")
    if not raw_operations:
        _fail(source, "operations", "must contain at least one operation")
    operation_ids: set[str] = set()
    operations: list[Mapping[str, Any]] = []
    for index, raw_operation in enumerate(raw_operations):
        field = f"operations[{index}]"
        operation = _mapping(raw_operation, source, field)
        _known_fields(operation, _OP_FIELDS, source, field)
        for required in ("id", "binding", "kind", "parameter_types", "return_type", "mutates"):
            if required not in operation:
                _fail(source, f"{field}.{required}", "is required")
        operation_id = _stable_id(operation.get("id"), source, f"{field}.id")
        if operation_id in operation_ids:
            _fail(source, f"{field}.id", f"duplicate operation ID {operation_id!r}")
        operation_ids.add(operation_id)
        if not isinstance(operation.get("binding"), str) or not operation["binding"]:
            _fail(source, f"{field}.binding", "must be a non-empty string")
        kind = operation.get("kind")
        if kind not in _KINDS:
            _fail(source, f"{field}.kind", f"must be one of {sorted(_KINDS)}")
        receiver = operation.get("receiver_type")
        if kind == "instance_method" and receiver not in type_ids:
            _fail(source, f"{field}.receiver_type", "must reference a declared type")
        if kind != "instance_method" and receiver is not None:
            _fail(source, f"{field}.receiver_type", "is only valid for instance methods")
        parameters = _list(operation.get("parameter_types"), source, f"{field}.parameter_types")
        for parameter_index, type_id in enumerate(parameters):
            if type_id not in type_ids:
                _fail(
                    source, f"{field}.parameter_types[{parameter_index}]",
                    "must reference a declared type",
                )
        return_type = operation.get("return_type")
        if return_type is not None and return_type not in type_ids:
            _fail(source, f"{field}.return_type", "must be null or reference a declared type")
        mutates = _list(operation.get("mutates"), source, f"{field}.mutates")
        input_count = len(parameters) + (kind == "instance_method")
        if any(type(index_) is not int or not 0 <= index_ < input_count for index_ in mutates):
            _fail(source, f"{field}.mutates", f"indexes must be in [0, {input_count})")
        if len(set(mutates)) != len(mutates):
            _fail(source, f"{field}.mutates", "must not contain duplicates")
        if operation.get("pure", False) and mutates:
            _fail(source, f"{field}.mutates", "must be empty when pure is true")
        if operation.get("exception_policy", "common_domain") not in _EXCEPTION_POLICIES:
            _fail(source, f"{field}.exception_policy", "has an unsupported policy")
        cost = operation.get("cost", 1)
        if type(cost) is not int or cost < 1:
            _fail(source, f"{field}.cost", "must be a positive integer")
        modes = operation.get("parameter_modes")
        if modes is not None:
            if not isinstance(modes, list) or len(modes) != len(parameters):
                _fail(source, f"{field}.parameter_modes", "must match parameter_types length")
            if any(mode not in _MODES for mode in modes):
                _fail(source, f"{field}.parameter_modes", "contains an unsupported mode")
        if operation.get("receiver_mode") not in _MODES | {None}:
            _fail(source, f"{field}.receiver_mode", "contains an unsupported mode")
        if language == "java" and kind != "constructor" and "(" not in operation["binding"]:
            _fail(source, f"{field}.binding", "Java method bindings must include parameter types")
        if "extensions" in operation:
            _extensions(operation["extensions"], source, f"{field}.extensions")
        operations.append(operation)

    raw_limits = _mapping(root.get("limits", {}), source, "limits")
    unknown_limits = sorted(set(raw_limits) - set(_LIMIT_DEFAULTS))
    if unknown_limits:
        _fail(source, "limits", f"unknown field(s): {', '.join(unknown_limits)}")
    limits = dict(_LIMIT_DEFAULTS)
    for name, value in raw_limits.items():
        minimum = 0 if name == "output_limit_bytes" else 1
        if type(value) is not int or value < minimum:
            _fail(source, f"limits.{name}", f"must be an integer >= {minimum}")
        limits[name] = value
    for campaign in ("discovery_tests", "validation_tests"):
        if limits["minimum_valid_samples"] > limits[campaign]:
            _fail(source, "limits.minimum_valid_samples", f"cannot exceed {campaign}")

    extensions = _extensions(root.get("extensions", {}), source, "extensions")
    return Manifest(
        source=source,
        language=language,
        target=target,
        types=tuple(types),
        operations=tuple(operations),
        limits=limits,
        extensions=extensions,
    )


def load_manifest(path: Path | str) -> Manifest:
    """Read and validate a TOML manifest. Target bindings are never imported."""

    source = Path(path)
    try:
        with source.open("rb") as stream:
            data = tomllib.load(stream)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise SpecValidationError(source, "$", str(exc)) from exc
    return validate_manifest(data, source)
