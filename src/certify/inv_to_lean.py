"""Print a DIG invariant as a Lean `Prop`.

Invariants are read through `inv.expr`, a z3 *syntax tree* (built by DIG's
parser from the invariant text; no solver is involved). The translation is
purely syntactic and in the trusted base, so it only accepts integer
arithmetic whose meaning coincides in z3 and Lean:

  * + - * (n-ary), unary -, `^` with a numeral exponent (expanded to
    products up to degree 6), numerals;
  * `div`/`mod` only by a nonzero numeral (z3 and Lean `Int` `/`, `%` are
    both Euclidean there; they differ only for a zero divisor);
  * comparisons, = and distinct, and/or/not/implies, `ite` (Bool-valued ite
    becomes `(c → a) ∧ (¬ c → b)`, Int-valued becomes `if c then a else b`).

Everything else (reals, arrays, uninterpreted functions, quantifiers,
variables not bound by the caller) raises `UnsupportedInv`.
"""

import z3


class UnsupportedInv(Exception):
    pass


_REL = {
    z3.Z3_OP_LE: "≤", z3.Z3_OP_LT: "<", z3.Z3_OP_GE: "≥", z3.Z3_OP_GT: ">",
    z3.Z3_OP_EQ: "=",
}


def _int_numeral(e: z3.ExprRef) -> int | None:
    if z3.is_int_value(e):
        return e.as_long()
    if z3.is_app_of(e, z3.Z3_OP_UMINUS) and z3.is_int_value(e.arg(0)):
        return -e.arg(0).as_long()
    return None


def to_lean(e: z3.ExprRef, env: dict[str, str]) -> str:
    """`env` maps z3 variable names to Lean `Int` terms."""
    srt = e.sort()
    if not (z3.is_int(e) or z3.is_bool(e)):
        raise UnsupportedInv(f"sort {srt} not supported")
    if z3.is_int_value(e):
        v = e.as_long()
        return str(v) if v >= 0 else f"({v})"
    if z3.is_true(e):
        return "True"
    if z3.is_false(e):
        return "False"
    if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        name = e.decl().name()
        if name not in env or not z3.is_int(e):
            raise UnsupportedInv(f"unbound variable {name}")
        return env[name]
    if not z3.is_app(e):
        raise UnsupportedInv(f"non-application {e}")
    k = e.decl().kind()
    a = [e.arg(i) for i in range(e.num_args())]
    t = lambda x: to_lean(x, env)  # noqa: E731

    match k:
        case z3.Z3_OP_ADD:
            return "(" + " + ".join(map(t, a)) + ")"
        case z3.Z3_OP_SUB:
            return "(" + " - ".join(map(t, a)) + ")"
        case z3.Z3_OP_MUL:
            return "(" + " * ".join(map(t, a)) + ")"
        case z3.Z3_OP_UMINUS:
            return f"(-{t(a[0])})"
        case z3.Z3_OP_POWER:
            n = _int_numeral(a[1])
            if n is None or n < 0 or n > 6:
                raise UnsupportedInv(f"exponent {a[1]}")
            if n == 0:
                return "1"
            b = t(a[0])
            return "(" + " * ".join([b] * n) + ")"
        case z3.Z3_OP_IDIV | z3.Z3_OP_MOD:
            d = _int_numeral(a[1])
            if d is None or d == 0:
                raise UnsupportedInv("division/modulo by a non-numeral or zero")
            op = "/" if k == z3.Z3_OP_IDIV else "%"
            return f"({t(a[0])} {op} {t(a[1])})"
        case _ if k in _REL:
            return f"({t(a[0])} {_REL[k]} {t(a[1])})"
        case z3.Z3_OP_DISTINCT:
            if len(a) != 2:
                raise UnsupportedInv("n-ary distinct")
            return f"({t(a[0])} ≠ {t(a[1])})"
        case z3.Z3_OP_AND:
            return "(" + " ∧ ".join(map(t, a)) + ")" if a else "True"
        case z3.Z3_OP_OR:
            return "(" + " ∨ ".join(map(t, a)) + ")" if a else "False"
        case z3.Z3_OP_NOT:
            return f"(¬ {t(a[0])})"
        case z3.Z3_OP_IMPLIES:
            return f"({t(a[0])} → {t(a[1])})"
        case z3.Z3_OP_ITE:
            c, x, y = map(t, a)
            if z3.is_bool(e):
                return f"(({c} → {x}) ∧ (¬ {c} → {y}))"
            return f"(if {c} then {x} else {y})"
        case _:
            raise UnsupportedInv(f"operator {e.decl().name()}")


def inv_to_lean(inv, env: dict[str, str]) -> str:
    """Translate a DIG `Inv` object (Eqt, Oct, MMP, Congruence, ...)."""
    try:
        e = inv.expr
    except Exception as ex:                      # noqa: BLE001
        raise UnsupportedInv(f"cannot build expr: {ex}") from ex
    if not isinstance(e, z3.ExprRef) or not z3.is_bool(e):
        raise UnsupportedInv("invariant is not a boolean expression")
    return to_lean(e, env)
