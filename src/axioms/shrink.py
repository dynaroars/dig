"""Deterministic type-aware shrinking for encoded recipes."""

from __future__ import annotations

from copy import deepcopy
from typing import Any, Iterator, Mapping


def shrink_value(value: Any) -> Iterator[Any]:
    """Yield simpler encoded values in deterministic order."""

    if isinstance(value, bool) or value is None:
        return
    if isinstance(value, int):
        seen: set[int] = set()
        candidates = [0]
        current = value
        while abs(current) > 1:
            current = int(current / 2)
            candidates.append(current)
        for candidate in candidates:
            if abs(candidate) < abs(value) and candidate not in seen:
                seen.add(candidate)
                yield candidate
        return
    if isinstance(value, str):
        if value:
            yield ""
        if len(value) > 1:
            yield value[: len(value) // 2]
        return
    if isinstance(value, list):
        if value:
            yield []
        chunk = len(value) // 2
        if chunk:
            yield value[:chunk]
            yield value[chunk:]
        for index, child in enumerate(value):
            for replacement in shrink_value(child):
                candidate = list(value)
                candidate[index] = replacement
                yield candidate
        return
    if isinstance(value, dict):
        for key in sorted(value):
            candidate = dict(value)
            del candidate[key]
            yield candidate
            for replacement in shrink_value(value[key]):
                candidate = dict(value)
                candidate[key] = replacement
                yield candidate


def shrink_recipe(recipe: Mapping[str, Any]) -> Iterator[dict[str, Any]]:
    """Shrink root values, then simplify distinct same-type roots into aliases."""

    roots = recipe.get("roots", [])
    for root_index, root in enumerate(roots):
        for value in shrink_value(root.get("value")):
            candidate = deepcopy(dict(recipe))
            candidate["roots"][root_index]["value"] = value
            yield candidate

    variables = recipe.get("variables", [])
    root_types = {root["id"]: root["type_id"] for root in roots}
    for index, variable in enumerate(variables):
        for earlier in variables[:index]:
            if earlier["type_id"] != variable["type_id"]:
                continue
            if earlier["root_id"] == variable["root_id"]:
                continue
            candidate = deepcopy(dict(recipe))
            old_root = candidate["variables"][index]["root_id"]
            candidate["variables"][index]["root_id"] = earlier["root_id"]
            if not any(item["root_id"] == old_root for item in candidate["variables"]):
                candidate["roots"] = [root for root in candidate["roots"] if root["id"] != old_root]
            # The root table is authoritative; guard malformed input while keeping
            # generated shrink moves well typed.
            if root_types[earlier["root_id"]] == variable["type_id"]:
                yield candidate
