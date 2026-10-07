"""Deterministic construction recipes for finite manifest values."""

from __future__ import annotations

from itertools import product
import random
import json
from typing import Any, Iterator, Mapping

from .aliases import alias_patterns
from .spec import Manifest


class RecipeGenerationError(ValueError):
    pass


def finite_recipes(
    manifest: Manifest,
    variables_by_type: Mapping[str, int],
    *,
    seed: int,
    limit: int | None,
) -> tuple[dict[str, Any], ...]:
    """Generate replayable recipes from explicitly declared finite values."""

    if limit is not None and limit < 1:
        raise RecipeGenerationError("recipe limit must be positive")
    declarations = {declaration["id"]: declaration for declaration in manifest.types}
    variable_keys = tuple(
        (type_id, index)
        for type_id in sorted(variables_by_type)
        for index in range(variables_by_type[type_id])
    )
    for type_id, count in variables_by_type.items():
        if count < 0:
            raise RecipeGenerationError(f"variable count for {type_id!r} is negative")
        if type_id not in declarations:
            raise RecipeGenerationError(f"unknown recipe type {type_id!r}")
        if count and not declarations[type_id].get("finite_values"):
            raise RecipeGenerationError(f"type {type_id!r} has no finite_values")

    candidates: list[dict[str, Any]] = []
    type_sequence = tuple(type_id for type_id, _index in variable_keys)
    for alias_assignment in alias_patterns(type_sequence):
        roots: dict[int, str] = {}
        root_types: dict[int, str] = {}
        for (type_id, _index), root_number in zip(variable_keys, alias_assignment, strict=True):
            roots.setdefault(root_number, f"r{root_number}")
            root_types[root_number] = type_id
        ordered_roots = tuple(sorted(roots))
        value_sets = [declarations[root_types[number]]["finite_values"] for number in ordered_roots]
        for values in product(*value_sets):
            recipe_number = len(candidates)
            candidates.append(
                {
                    "recipe_id": f"finite-{recipe_number:06d}",
                    "roots": [
                        {
                            "id": roots[number],
                            "type_id": root_types[number],
                            "value": value,
                        }
                        for number, value in zip(ordered_roots, values, strict=True)
                    ],
                    "variables": [
                        {
                            "type_id": type_id,
                            "index": index,
                            "root_id": roots[root_number],
                        }
                        for (type_id, index), root_number in zip(
                            variable_keys, alias_assignment, strict=True
                        )
                    ],
                }
            )
    generator = random.Random(seed)
    generator.shuffle(candidates)
    selected = candidates if limit is None else candidates[:limit]
    # IDs describe the selected deterministic campaign rather than pre-shuffle order.
    for index, recipe in enumerate(selected):
        recipe["recipe_id"] = f"seed-{seed}-case-{index:06d}"
    return tuple(selected)


def variables_in_term_data(term: Mapping[str, Any]) -> Iterator[tuple[str, int]]:
    kind = term.get("kind")
    if kind == "variable":
        yield term["type_id"], term["index"]
    elif kind == "call":
        for child in term.get("children", ()):
            yield from variables_in_term_data(child)


def sampled_recipes(
    values_by_type: Mapping[str, list[Any]],
    variables_by_type: Mapping[str, int],
    *,
    seed: int,
    limit: int,
    exclude: set[str] | None = None,
) -> tuple[dict[str, Any], ...]:
    """Sample bounded, distinct recipes without constructing a Cartesian product."""

    if limit < 1:
        raise RecipeGenerationError("recipe limit must be positive")
    for type_id, count in variables_by_type.items():
        if count and not values_by_type.get(type_id):
            raise RecipeGenerationError(f"type {type_id!r} has no recipe values")
    variable_keys = tuple(
        (type_id, index)
        for type_id in sorted(variables_by_type)
        for index in range(variables_by_type[type_id])
    )
    patterns = tuple(alias_patterns(tuple(type_id for type_id, _index in variable_keys)))
    generator = random.Random(seed)
    seen = set(exclude or ())
    selected: list[dict[str, Any]] = []
    attempts = 0
    max_attempts = max(1_000, limit * 100)
    while len(selected) < limit and attempts < max_attempts:
        pattern = patterns[attempts % len(patterns)] if patterns else ()
        root_types: dict[int, str] = {}
        for (type_id, _index), root_number in zip(variable_keys, pattern, strict=True):
            root_types[root_number] = type_id
        roots = []
        for root_number in sorted(root_types):
            type_id = root_types[root_number]
            pool = values_by_type[type_id]
            # Cycle first for boundary coverage, then use the explicit RNG stream.
            cycle = attempts // max(1, len(patterns))
            value_index = cycle % len(pool) if cycle < len(pool) else generator.randrange(len(pool))
            roots.append(
                {"id": f"r{root_number}", "type_id": type_id, "value": pool[value_index]}
            )
        recipe = {
            "recipe_id": f"seed-{seed}-case-{len(selected):06d}",
            "roots": roots,
            "variables": [
                {"type_id": type_id, "index": index, "root_id": f"r{root_number}"}
                for (type_id, index), root_number in zip(variable_keys, pattern, strict=True)
            ],
        }
        key = recipe_key(recipe)
        if key not in seen:
            seen.add(key)
            selected.append(recipe)
        attempts += 1
    return tuple(selected)


def recipe_key(recipe: Mapping[str, Any]) -> str:
    return json.dumps(
        {"roots": recipe.get("roots", []), "variables": recipe.get("variables", [])},
        ensure_ascii=False,
        allow_nan=False,
        sort_keys=True,
        separators=(",", ":"),
    )
