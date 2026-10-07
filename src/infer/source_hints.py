"""Polynomial candidate hints from actual C guards and additive updates."""
from functools import lru_cache
from pathlib import Path

import sympy
from pycparser import c_ast, c_parser


def expression(node):
    if isinstance(node, c_ast.ID):
        return sympy.Symbol(node.name)
    if isinstance(node, c_ast.Constant) and node.type == "int":
        return sympy.Integer(int(node.value, 0))
    if isinstance(node, c_ast.UnaryOp) and node.op in ("+", "-"):
        value = expression(node.expr)
        return value if node.op == "+" else -value
    if isinstance(node, c_ast.BinaryOp) and node.op in ("+", "-", "*"):
        left, right = expression(node.left), expression(node.right)
        return {"+": lambda: left + right, "-": lambda: left - right,
                "*": lambda: left * right}[node.op]()
    raise ValueError("not a supported polynomial expression")


@lru_cache(maxsize=16)
def _candidates(text):
    from data.symex_c import _preprocess
    guards, updates = set(), set()
    class Visitor(c_ast.NodeVisitor):
        def visit_BinaryOp(self, node):
            if node.op in ("<", "<=", ">", ">=", "==", "!="):
                try:
                    guards.add(sympy.expand(expression(node.left) - expression(node.right)))
                except (ValueError, TypeError):
                    pass
            self.generic_visit(node)

        def visit_Assignment(self, node):
            try:
                left, right = expression(node.lvalue), expression(node.rvalue)
                delta = right - left if node.op == "=" else right if node.op == "+=" else -right
                if node.op in ("=", "+=", "-=") and left not in delta.free_symbols:
                    updates.add((left, sympy.expand(delta)))
            except (ValueError, TypeError):
                pass
            self.generic_visit(node)

    tree = c_parser.CParser().parse(_preprocess(text))
    for node in tree.ext:
        if isinstance(node, c_ast.FuncDef) and node.decl.name == "mainQ":
            Visitor().visit(node.body)
    result = set(guards)
    for guard in guards:
        for variable, delta in updates:
            if variable in guard.free_symbols:
                result.update((sympy.expand(guard + delta), sympy.expand(guard - delta)))
    # Constants change a bound, not the expression being bounded. Avoid
    # checking dozens of shifted versions of the same objective.
    canonical = set()
    for term in result:
        if term.free_symbols:
            term = sympy.expand(term - term.xreplace({s: 0 for s in term.free_symbols}))
            _, primitive = sympy.Poly(term, *sorted(term.free_symbols, key=str)).primitive()
            canonical.add(primitive.as_expr())
    return frozenset(canonical)


def polynomial_terms(source: Path | None, symbols, budget, degree=1):
    if source is None:
        return set()
    try:
        candidates = _candidates(source.read_text())
    except (ValueError, TypeError, OSError):
        return set()
    allowed = set(symbols)
    selected = []
    for term in sorted(candidates, key=lambda p: (sympy.count_ops(p), str(p))):
        if term.free_symbols.issubset(allowed) and len(term.free_symbols) <= 3:
            if sympy.Poly(term, *symbols).total_degree() <= degree:
                selected.append(term)
    return {sign * term for term in selected[:budget // 2] for sign in (-1, 1)}
