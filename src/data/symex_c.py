"""
Python symbolic execution engine for simple C programs.

Replaces CIVL in DIG for invariant inference on programs using:
  - Integer arithmetic (+ - * / %)
  - while loops with break
  - if/else branching
  - vassume(cond) for preconditions
  - vtraceN(...) for observation points

Output format matches what PathCondCIVL.parse() expects (already replace_str'd).

Usage (standalone):
    python symex_c.py cohendiv.c --maxdepth 20
"""

from __future__ import annotations

import copy
import sys
import argparse
import operator as op_module
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path

import z3
from pycparser import c_ast, c_parser

# ─────────────────────────────────────────────────────────── helpers ──

def _sympy_to_z3_int(name: str) -> z3.ArithRef:
    return z3.Int(name)


def _z3_to_py_str(expr: z3.ExprRef) -> str:
    """
    Convert a Z3 arithmetic/boolean expression to a Python-expression string
    that Z3.parse() (in z3utils.py) can round-trip back to a Z3 expr.

    Z3.parse() evaluates the string with Python's ast module, where bare
    identifiers become z3.Int(name), so we only need valid Python syntax.
    """
    if z3.is_int_value(expr):
        v = expr.as_long()
        return f"({v})" if v < 0 else str(v)

    if z3.is_const(expr) and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        return expr.decl().name()

    kind = expr.decl().kind()
    children = expr.children()

    if kind == z3.Z3_OP_ADD:
        parts = [_z3_to_py_str(c) for c in children]
        return "(" + " + ".join(parts) + ")"

    if kind == z3.Z3_OP_MUL:
        parts = [_z3_to_py_str(c) for c in children]
        return "(" + " * ".join(parts) + ")"

    if kind == z3.Z3_OP_SUB:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} - {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_UMINUS:
        return f"(-{_z3_to_py_str(children[0])})"

    if kind == z3.Z3_OP_IDIV or kind == z3.Z3_OP_DIV:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} / {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_MOD:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} % {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_LE:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} <= {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_LT:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} < {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_GE:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} >= {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_GT:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} > {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_EQ:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} == {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_DISTINCT:
        lhs, rhs = children
        return f"({_z3_to_py_str(lhs)} != {_z3_to_py_str(rhs)})"

    if kind == z3.Z3_OP_AND:
        parts = [_z3_to_py_str(c) for c in children]
        return "(" + " and ".join(parts) + ")"

    if kind == z3.Z3_OP_OR:
        parts = [_z3_to_py_str(c) for c in children]
        return "(" + " or ".join(parts) + ")"

    if kind == z3.Z3_OP_NOT:
        inner = children[0]
        ikind = inner.decl().kind()
        ic = inner.children()
        # Push negation into comparison to produce cleaner output without `not`
        flip = {
            z3.Z3_OP_LE: ">",
            z3.Z3_OP_LT: ">=",
            z3.Z3_OP_GE: "<",
            z3.Z3_OP_GT: "<=",
            z3.Z3_OP_EQ: "!=",
            z3.Z3_OP_DISTINCT: "==",
        }
        if ikind in flip and len(ic) == 2:
            return f"({_z3_to_py_str(ic[0])} {flip[ikind]} {_z3_to_py_str(ic[1])})"
        return f"(not {_z3_to_py_str(children[0])})"

    if kind == z3.Z3_OP_TRUE:
        return "True"

    if kind == z3.Z3_OP_FALSE:
        return "False"

    # Fallback
    return str(expr)


# ─────────────────────────────────────────────────── symbolic state ──

class Exit(Enum):
    NORMAL = auto()
    BREAK = auto()
    CONTINUE = auto()
    RETURN = auto()


@dataclass
class SymState:
    """One symbolic execution path."""
    env: dict[str, z3.ExprRef] = field(default_factory=dict)
    pc: list[z3.ExprRef] = field(default_factory=list)
    loop_depth: int = 0
    exit: Exit = Exit.NORMAL

    # ── copying helpers ──────────────────────────────────────────────

    def _copy(self) -> SymState:
        return SymState(
            env=dict(self.env),
            pc=list(self.pc),
            loop_depth=self.loop_depth,
            exit=self.exit,
        )

    def add_constraint(self, cond: z3.ExprRef) -> SymState:
        s = self._copy()
        s.pc.append(z3.simplify(cond))
        return s

    def set_var(self, name: str, val: z3.ExprRef) -> SymState:
        s = self._copy()
        s.env[name] = z3.simplify(val)
        return s

    def with_exit(self, reason: Exit) -> SymState:
        s = self._copy()
        s.exit = reason
        return s

    def inc_loop(self) -> SymState:
        s = self._copy()
        s.loop_depth += 1
        return s

    def reset_exit(self) -> SymState:
        s = self._copy()
        s.exit = Exit.NORMAL
        return s

    # ── smt2 serialisation ───────────────────────────────────────────

    def pc_str(self) -> str | None:
        """Path condition as a Z3.parse()-compatible Python expression, or None."""
        if not self.pc:
            return None
        parts = [_z3_to_py_str(c) for c in self.pc]
        if len(parts) == 1:
            return parts[0]
        return "(" + " and ".join(parts) + ")"

    def slocal_str(self, param_names: list[str]) -> str:
        """
        slocal as a Z3.parse()-compatible Python expression.
        Only includes variables that appear in the vtrace param list.
        """
        parts = []
        for name in param_names:
            val = self.env.get(name)
            if val is None:
                continue
            parts.append(f"{name} == {_z3_to_py_str(val)}")
        return " and ".join(parts)


# ─────────────────────────────────────────────────── path record ──

@dataclass
class PathRecord:
    loc: str
    param_names: list[str]
    env_snapshot: dict[str, z3.ExprRef]
    pc_snapshot: list[z3.ExprRef]


# ─────────────────────────────────────────────── symex engine ──────

class CSymEx:
    """
    Symbolic execution engine for a small subset of C.

    After calling run(), self.records holds one PathRecord per
    vtrace observation collected along every feasible symbolic path.
    """

    MAX_STATES = 5000  # hard cap on total active states to prevent explosion
    SOLVER_TIMEOUT_MS = 3000

    def __init__(self, filename: Path, max_depth: int) -> None:
        self.filename = filename
        self.max_depth = max_depth
        self.records: list[PathRecord] = []

        # Solver for feasibility (reused with push/pop)
        self.solver = z3.Solver()
        self.solver.set("timeout", self.SOLVER_TIMEOUT_MS)

        # Populated by _parse():
        self.mainq_params: list[tuple[str, str]] = []   # [(name, type), ...]
        self.vtrace_params: dict[str, list[str]] = {}   # {func_name: [param_names]}
        self.func_bodies: dict[str, c_ast.Compound] = {}

    # ── public ───────────────────────────────────────────────────────

    def run(self) -> list[tuple[str, str | None, str]]:
        """
        Execute symbolically.

        Returns list of (loc, pc_str, slocal_str) tuples ready for
        SymStatesMaker.merge() — i.e., already replace_str'd Python exprs.
        """
        ast = self._parse()
        init_state = self._make_init_state()
        self._exec_compound(self.func_bodies["mainQ"], [init_state])
        return self._format_records()

    # ── parsing ───────────────────────────────────────────────────────

    def _parse(self) -> c_ast.FileAST:
        src = self.filename.read_text()
        src = _strip_comments(src)
        src = _strip_includes(src)

        parser = c_parser.CParser()
        ast = parser.parse(src)

        for node in ast.ext:
            if not isinstance(node, c_ast.FuncDef):
                continue
            name = node.decl.name
            self.func_bodies[name] = node.body

            if name == "mainQ" and node.decl.type.args:
                self.mainq_params = [
                    (p.name, p.type.type.names[0])
                    for p in node.decl.type.args.params
                ]

            if name.startswith("vtrace") and node.decl.type.args:
                self.vtrace_params[name] = [
                    p.name for p in node.decl.type.args.params
                ]

        assert "mainQ" in self.func_bodies, "mainQ not found in C file"
        return ast

    def _make_init_state(self) -> SymState:
        state = SymState()
        for name, _ in self.mainq_params:
            state.env[name] = z3.Int(f"X_{name}")
        return state

    # ── statement execution ───────────────────────────────────────────

    def _exec_compound(self,
                       node: c_ast.Compound,
                       states: list[SymState]) -> list[SymState]:
        if not node or not node.block_items:
            return states

        active = states
        done: list[SymState] = []

        for stmt in node.block_items:
            if not active:
                break
            new_states = self._exec_stmt(stmt, active)
            active = []
            for s in new_states:
                if s.exit == Exit.NORMAL:
                    active.append(s)
                else:
                    done.append(s)

        return done + active

    def _exec_stmt(self,
                   node: c_ast.Node,
                   states: list[SymState]) -> list[SymState]:
        if not states:
            return []

        if isinstance(node, c_ast.Compound):
            return self._exec_compound(node, states)

        if isinstance(node, c_ast.Decl):
            return self._exec_decl(node, states)

        if isinstance(node, c_ast.Assignment):
            return self._exec_assign(node, states)

        if isinstance(node, c_ast.If):
            return self._exec_if(node, states)

        if isinstance(node, c_ast.While):
            return self._exec_while(node, states)

        if isinstance(node, c_ast.For):
            return self._exec_for(node, states)

        if isinstance(node, c_ast.FuncCall):
            return self._exec_call(node, states)

        if isinstance(node, c_ast.Break):
            return [s.with_exit(Exit.BREAK) for s in states]

        if isinstance(node, c_ast.Continue):
            return [s.with_exit(Exit.CONTINUE) for s in states]

        if isinstance(node, c_ast.Return):
            return [s.with_exit(Exit.RETURN) for s in states]

        # Unary expression statement (e.g., i++, i--)
        if isinstance(node, c_ast.UnaryOp) and node.op in ("p++", "p--", "++p", "--p"):
            return self._exec_incr_stmt(node, states)

        # Unknown: pass through
        return states

    def _exec_decl(self,
                   node: c_ast.Decl,
                   states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            if node.init is not None:
                val = self._eval_expr(node.init, state)
            else:
                # Uninitialised — use a fresh symbolic var
                val = z3.Int(f"_uninit_{node.name}")
            result.append(state.set_var(node.name, val))
        return result

    def _exec_assign(self,
                     node: c_ast.Assignment,
                     states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            rhs = self._eval_expr(node.rvalue, state)
            if node.op == "=":
                val = rhs
            else:
                lhs = self._eval_expr(node.lvalue, state)
                compound = {
                    "+=": lhs + rhs,
                    "-=": lhs - rhs,
                    "*=": lhs * rhs,
                    "/=": lhs / rhs,
                    "%=": lhs % rhs,
                }
                val = compound.get(node.op, rhs)
            target = node.lvalue.name if isinstance(node.lvalue, c_ast.ID) else None
            if target:
                result.append(state.set_var(target, val))
            else:
                result.append(state)
        return result

    def _exec_incr_stmt(self,
                        node: c_ast.UnaryOp,
                        states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            if not isinstance(node.expr, c_ast.ID):
                result.append(state)
                continue
            name = node.expr.name
            cur = self._eval_expr(node.expr, state)
            if node.op in ("p++", "++p"):
                new_val = cur + z3.IntVal(1)
            else:
                new_val = cur - z3.IntVal(1)
            result.append(state.set_var(name, new_val))
        return result

    def _exec_if(self,
                 node: c_ast.If,
                 states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            cond = self._eval_expr(node.cond, state)

            # True branch
            true_state = state.add_constraint(cond)
            if self._feasible(true_state):
                then_states = self._exec_stmt(node.iftrue, [true_state])
                result.extend(then_states)

            # False branch
            false_state = state.add_constraint(z3.Not(cond))
            if self._feasible(false_state):
                if node.iffalse:
                    else_states = self._exec_stmt(node.iffalse, [false_state])
                    result.extend(else_states)
                else:
                    result.append(false_state)

        return result

    def _exec_while(self,
                    node: c_ast.While,
                    states: list[SymState],
                    _iter: int = 0) -> list[SymState]:
        """
        Unroll the while loop up to max_depth total iterations.
        Each unique state tracks its own loop_depth so paths share depth budgets.
        """
        if not states:
            return []

        # Hard cap to prevent explosion
        if len(states) > self.MAX_STATES:
            states = states[:self.MAX_STATES]

        result: list[SymState] = []       # states that exited the loop
        continuing: list[SymState] = []   # states that re-enter

        cond_is_true = _is_const_true(node.cond)

        for state in states:
            if state.loop_depth >= self.max_depth:
                # Depth exhausted: treat loop as terminated
                if not cond_is_true:
                    exit_s = state.add_constraint(z3.Not(self._eval_expr(node.cond, state)))
                    if self._feasible(exit_s):
                        result.append(exit_s)
                # else: while(1) at max depth — dead path, discard
                continue

            if cond_is_true:
                # while(1): only break exits
                body_states = self._exec_compound(node.stmt, [state.inc_loop()])
                for s in body_states:
                    if s.exit == Exit.BREAK:
                        result.append(s.reset_exit())
                    elif s.exit == Exit.CONTINUE:
                        continuing.append(s.reset_exit())
                    elif s.exit == Exit.NORMAL:
                        continuing.append(s)
                    else:  # RETURN
                        result.append(s)
            else:
                cond = self._eval_expr(node.cond, state)

                # Exit branch (condition false)
                exit_s = state.add_constraint(z3.Not(cond))
                if self._feasible(exit_s):
                    result.append(exit_s)

                # Enter branch (condition true)
                enter_s = state.add_constraint(cond).inc_loop()
                if self._feasible(enter_s):
                    body_states = self._exec_compound(node.stmt, [enter_s])
                    for s in body_states:
                        if s.exit == Exit.BREAK:
                            result.append(s.reset_exit())
                        elif s.exit == Exit.CONTINUE:
                            continuing.append(s.reset_exit())
                        elif s.exit == Exit.NORMAL:
                            continuing.append(s)
                        else:
                            result.append(s)

        # Recurse for states re-entering the loop
        result.extend(self._exec_while(node, continuing, _iter + 1))
        return result

    def _exec_for(self,
                  node: c_ast.For,
                  states: list[SymState]) -> list[SymState]:
        # Desugar: init; while(cond) { body; next; }
        if node.init:
            states = self._exec_stmt(node.init, states)

        cond = node.cond or c_ast.Constant("int", "1")
        body_items = node.stmt.block_items or [] if isinstance(node.stmt, c_ast.Compound) else [node.stmt]
        if node.next:
            body_items = body_items + [node.next]

        fake_while = c_ast.While(cond=cond, stmt=c_ast.Compound(block_items=body_items))
        return self._exec_while(fake_while, states)

    def _exec_call(self,
                   node: c_ast.FuncCall,
                   states: list[SymState]) -> list[SymState]:
        fname = node.name.name if isinstance(node.name, c_ast.ID) else None
        if fname is None:
            return states

        if fname == "vassume":
            result = []
            for state in states:
                cond = self._eval_expr(node.args.exprs[0], state)
                new_state = state.add_constraint(cond)
                if self._feasible(new_state):
                    result.append(new_state)
            return result

        if fname.startswith("vtrace") and fname in self.vtrace_params:
            params = self.vtrace_params[fname]
            for state in states:
                vals = {}
                for pname, arg in zip(params,
                                      node.args.exprs if node.args else []):
                    vals[pname] = self._eval_expr(arg, state)
                self.records.append(PathRecord(
                    loc=fname,
                    param_names=params,
                    env_snapshot=vals,
                    pc_snapshot=list(state.pc),
                ))
            return states

        # Ignore: printf, atoi, unknown functions
        return states

    # ── expression evaluation ─────────────────────────────────────────

    def _eval_expr(self, node: c_ast.Node, state: SymState) -> z3.ExprRef:
        if isinstance(node, c_ast.Constant):
            return z3.IntVal(int(node.value))

        if isinstance(node, c_ast.ID):
            v = state.env.get(node.name)
            if v is None:
                # Treat as a fresh symbolic var (handles forward-declared globals)
                v = z3.Int(node.name)
            return v

        if isinstance(node, c_ast.UnaryOp):
            return self._eval_unary(node, state)

        if isinstance(node, c_ast.BinaryOp):
            return self._eval_binary(node, state)

        if isinstance(node, c_ast.Cast):
            return self._eval_expr(node.expr, state)

        if isinstance(node, c_ast.ExprList):
            # Comma expression: evaluate all, return last
            result = z3.IntVal(0)
            for e in node.exprs:
                result = self._eval_expr(e, state)
            return result

        raise NotImplementedError(f"Unsupported expression: {type(node).__name__}: {node}")

    def _eval_unary(self, node: c_ast.UnaryOp, state: SymState) -> z3.ExprRef:
        # p++ and ++p as expressions return the (pre/post) value
        if node.op in ("p++", "++p", "p--", "--p"):
            return self._eval_expr(node.expr, state)

        operand = self._eval_expr(node.expr, state)
        ops = {
            "-": lambda x: -x,
            "+": lambda x: x,
            "!": lambda x: z3.Not(x) if z3.is_bool(x) else z3.Not(x != 0),
            "~": lambda x: -x - 1,  # bitwise NOT approximation for integers
        }
        fn = ops.get(node.op)
        if fn is None:
            raise NotImplementedError(f"Unary op '{node.op}' not supported")
        return fn(operand)

    def _eval_binary(self, node: c_ast.BinaryOp, state: SymState) -> z3.ExprRef:
        # Short-circuit: defer right-side eval for && and ||
        if node.op == "&&":
            lhs = self._eval_expr(node.left, state)
            rhs = self._eval_expr(node.right, state)
            return z3.And(lhs, rhs)
        if node.op == "||":
            lhs = self._eval_expr(node.left, state)
            rhs = self._eval_expr(node.right, state)
            return z3.Or(lhs, rhs)

        lhs = self._eval_expr(node.left, state)
        rhs = self._eval_expr(node.right, state)

        arith = {
            "+": op_module.add,
            "-": op_module.sub,
            "*": op_module.mul,
            "/": op_module.truediv,   # integer division in Z3
            "%": op_module.mod,
        }
        cmp = {
            "<":  op_module.lt,
            "<=": op_module.le,
            ">":  op_module.gt,
            ">=": op_module.ge,
            "==": op_module.eq,
            "!=": op_module.ne,
        }
        if node.op in arith:
            return arith[node.op](lhs, rhs)
        if node.op in cmp:
            return cmp[node.op](lhs, rhs)

        raise NotImplementedError(f"Binary op '{node.op}' not supported")

    # ── feasibility ───────────────────────────────────────────────────

    def _feasible(self, state: SymState) -> bool:
        if not state.pc:
            return True
        self.solver.push()
        for c in state.pc:
            self.solver.add(c)
        result = self.solver.check()
        self.solver.pop()
        # If unknown (timeout), be optimistic and keep the path
        return result != z3.unsat

    # ── output formatting ─────────────────────────────────────────────

    def _format_records(self) -> list[tuple[str, str | None, str]]:
        """
        Return list of (loc, pc_str_or_None, slocal_str) tuples.

        pc_str is a Python expression string (or None if unconstrained)
        that Z3.parse() can evaluate.
        slocal_str is a conjunction of `var == expr` equalities.
        """
        out = []
        for rec in self.records:
            # Build a temp SymState to reuse slocal_str logic
            s = SymState(env=rec.env_snapshot, pc=rec.pc_snapshot)
            pc_str = s.pc_str()
            slocal_str = s.slocal_str(rec.param_names)
            if slocal_str:
                out.append((rec.loc, pc_str, slocal_str))
        return out


# ─────────────────────────────────────────────── utilities ──────────

def _strip_comments(src: str) -> str:
    import re
    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE,
    )
    return re.sub(pattern, lambda m: " " if m.group(0).startswith("/") else m.group(0), src)


def _strip_includes(src: str) -> str:
    """Remove #include lines so pycparser doesn't need system headers."""
    lines = [l for l in src.splitlines() if not l.strip().startswith("#include")]
    return "\n".join(lines)


def _is_const_true(node: c_ast.Node) -> bool:
    return isinstance(node, c_ast.Constant) and node.value == "1"


# ──────────────────────────────────────── CIVL-compatible text output ──

def run_and_print(filename: Path, max_depth: int) -> None:
    """
    Run symex and print output in CIVL-compatible text format:

        vtrace1: q = 0; r = X_x; ...
        path condition: (0 <= X_x - 1) and (0 <= X_y - 1)
        ...
    """
    engine = CSymEx(filename, max_depth)
    results = engine.run()

    for loc, pc_str, slocal_str in results:
        # Convert slocal `q == 0 and r == X_x ...` back to CIVL-ish
        # format:  `vtrace1: q = 0; r = X_x; ...`
        # We emit Python-expr format with a special prefix so
        # PathCondPython.parse_parts() can pick it up.
        slocal_civl = slocal_str.replace(" == ", " = ").replace(" and ", "; ")
        pc_civl = "true" if pc_str is None else pc_str.replace(" and ", "&&")
        print(f"{loc}: {slocal_civl}")
        print(f"path condition: {pc_civl}")


# ──────────────────────────────────────────────────── CLI entry point ──

def main() -> None:
    p = argparse.ArgumentParser(description="Python symbolic execution for C")
    p.add_argument("filename", type=Path)
    p.add_argument("-maxdepth", type=int, default=20)
    args = p.parse_args()
    run_and_print(args.filename, args.maxdepth)


if __name__ == "__main__":
    main()
