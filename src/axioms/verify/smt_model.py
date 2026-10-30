"""Sound verification of pure axioms against user-supplied logical models."""

from __future__ import annotations

import hashlib
from typing import Any, Mapping

import z3

from ..model import (
    Call,
    Constant,
    Equation,
    ReturnProjection,
    Term,
    Variable,
    canonical_json,
    equation_to_data,
)
from ..spec import Manifest
from .base import ProofStatus, VerificationResult


_EXTENSION = "org.dynaroars.dig.smt"


class SmtModelVerifier:
    name = "dig-smt-model"
    version = "1"

    def supports(self, manifest: Manifest, equation: Equation) -> tuple[bool, str]:
        type_sorts = self._type_sorts(manifest)
        operations = {declaration["id"]: declaration for declaration in manifest.operations}
        for term in _walk(equation):
            if term.type_id not in type_sorts:
                return False, f"type {term.type_id!r} has no SMT sort"
            if isinstance(term, Call):
                declaration = operations.get(term.operation_id)
                model = (declaration or {}).get("extensions", {}).get(_EXTENSION)
                if declaration is None or not declaration.get("pure", False):
                    return False, f"operation {term.operation_id!r} is not declared pure"
                if not isinstance(term.projection, ReturnProjection):
                    return False, "SMT model verifier v1 supports return projections only"
                if not isinstance(model, Mapping) or "result" not in model:
                    return False, f"operation {term.operation_id!r} has no SMT result model"
        return True, "all terms have pure scalar logical models"

    def verify(self, manifest: Manifest, equation: Equation) -> VerificationResult:
        supported, detail = self.supports(manifest, equation)
        if not supported:
            return self._result(ProofStatus.UNKNOWN, detail=detail)
        type_sorts = self._type_sorts(manifest)
        declarations = {declaration["id"]: declaration for declaration in manifest.operations}
        variables: dict[tuple[str, int], z3.ExprRef] = {}
        assumptions: list[z3.BoolRef] = []

        def translate(term: Term) -> z3.ExprRef:
            if isinstance(term, Variable):
                key = (term.type_id, term.index)
                if key not in variables:
                    variables[key] = z3.Const(
                        f"{term.type_id}_{term.index}", _sort(type_sorts[term.type_id])
                    )
                return variables[key]
            if isinstance(term, Constant):
                return _constant(term.value, type_sorts[term.type_id])
            declaration = declarations[term.operation_id]
            model = declaration["extensions"][_EXTENSION]
            arguments = [translate(child) for child in term.children]
            if "precondition" in model:
                assumptions.append(_expression(model["precondition"], arguments))
            return _expression(model["result"], arguments)

        lhs = translate(equation.lhs)
        rhs = translate(equation.rhs)
        solver = z3.Solver()
        solver.add(*assumptions)
        solver.add(lhs != rhs)
        status = solver.check()
        if status == z3.unsat:
            return self._result(
                ProofStatus.PROVED,
                assumptions=("user-supplied logical operation models",),
                detail="negated model equation is unsatisfiable",
                equation=equation,
            )
        if status == z3.unknown:
            return self._result(
                ProofStatus.UNKNOWN,
                detail="solver returned unknown: " + solver.reason_unknown(),
                equation=equation,
            )
        model = solver.model()
        roots = []
        recipe_variables = []
        for root_number, ((type_id, index), symbol) in enumerate(sorted(variables.items())):
            value = _model_value(model.eval(symbol, model_completion=True))
            root_id = f"r{root_number}"
            roots.append({"id": root_id, "type_id": type_id, "value": value})
            recipe_variables.append(
                {"type_id": type_id, "index": index, "root_id": root_id}
            )
        counterexample = {
            "recipe": {
                "recipe_id": "smt-model-counterexample",
                "roots": roots,
                "variables": recipe_variables,
            },
            "replay_id": "smt-model-counterexample",
        }
        return self._result(
            ProofStatus.REFUTED,
            counterexample=counterexample,
            detail="solver found a model counterexample",
            equation=equation,
        )

    @staticmethod
    def _type_sorts(manifest: Manifest) -> Mapping[str, str]:
        extension = manifest.extensions.get(_EXTENSION, {})
        if not isinstance(extension, Mapping):
            return {}
        sorts = extension.get("type_sorts", {})
        return sorts if isinstance(sorts, Mapping) else {}

    def _result(
        self,
        status: ProofStatus,
        *,
        assumptions: tuple[str, ...] = (),
        counterexample: dict[str, Any] | None = None,
        detail: str | None = None,
        equation: Equation | None = None,
    ) -> VerificationResult:
        artifact = canonical_json(
            {
                "status": status.value,
                "scope": "model",
                "detail": detail,
                "equation": equation_to_data(equation) if equation is not None else None,
                "counterexample": counterexample,
            }
        )
        return VerificationResult(
            status=status,
            verifier=self.name,
            version=self.version,
            scope="model",
            cases_checked=0,
            valid_cases=0,
            invalid_domain_cases=0,
            assumptions=assumptions,
            artifact_digest="sha256:" + hashlib.sha256(artifact.encode()).hexdigest(),
            counterexample=counterexample,
            detail=detail,
        )


def _walk(equation: Equation):
    def visit(term: Term):
        yield term
        if isinstance(term, Call):
            for child in term.children:
                yield from visit(child)

    yield from visit(equation.lhs)
    yield from visit(equation.rhs)


def _sort(name: str) -> z3.SortRef:
    if name == "int":
        return z3.IntSort()
    if name == "real":
        return z3.RealSort()
    if name == "bool":
        return z3.BoolSort()
    raise ValueError(f"unsupported SMT sort {name!r}")


def _constant(value: Any, sort: str) -> z3.ExprRef:
    if sort == "bool" and isinstance(value, bool):
        return z3.BoolVal(value)
    if sort == "int" and type(value) is int:
        return z3.IntVal(value)
    if sort == "real" and isinstance(value, (int, float)) and not isinstance(value, bool):
        return z3.RealVal(str(value))
    raise ValueError(f"constant {value!r} is incompatible with SMT sort {sort}")


def _expression(expression: Mapping[str, Any], arguments: list[z3.ExprRef]) -> z3.ExprRef:
    kind = expression.get("kind")
    if kind == "arg":
        return arguments[expression["index"]]
    if kind == "const":
        value = expression["value"]
        if isinstance(value, bool):
            return z3.BoolVal(value)
        if type(value) is int:
            return z3.IntVal(value)
        return z3.RealVal(str(value))
    children = [_expression(child, arguments) for child in expression.get("args", ())]
    if kind == "add":
        return sum(children)
    if kind == "sub" and len(children) == 2:
        return children[0] - children[1]
    if kind == "mul":
        result = children[0]
        for child in children[1:]:
            result *= child
        return result
    if kind == "neg" and len(children) == 1:
        return -children[0]
    if kind == "eq" and len(children) == 2:
        return children[0] == children[1]
    if kind == "lt" and len(children) == 2:
        return children[0] < children[1]
    if kind == "le" and len(children) == 2:
        return children[0] <= children[1]
    if kind == "and":
        return z3.And(*children)
    if kind == "or":
        return z3.Or(*children)
    if kind == "not" and len(children) == 1:
        return z3.Not(children[0])
    if kind == "ite" and len(children) == 3:
        return z3.If(*children)
    raise ValueError(f"unsupported SMT model expression {kind!r}")


def _model_value(value: z3.ExprRef) -> Any:
    if z3.is_true(value):
        return True
    if z3.is_false(value):
        return False
    if z3.is_int_value(value):
        return value.as_long()
    if z3.is_rational_value(value):
        numerator = value.numerator_as_long()
        denominator = value.denominator_as_long()
        return numerator if denominator == 1 else {"$rational": [numerator, denominator]}
    return str(value)
