"""
Python symbolic execution engine for simple C programs.

Handles invariant inference on programs using:
  - Integer arithmetic (+ - * / %)
  - while loops with break
  - if/else branching
  - vassume(cond) for preconditions
  - vtraceN(...) for observation points

run() returns z3 path conditions directly (consumed in-process by
SymStatesMakerC), so no text serialization/parsing round-trip is needed.
"""

from __future__ import annotations

import copy
import operator as op_module
from dataclasses import dataclass, field
from enum import Enum, auto
from pathlib import Path

import z3
from pycparser import c_ast, c_parser

# ─────────────────────────────────────────────────────────── helpers ──

_REAL = z3.RealSort()


def _is_real(e: z3.ExprRef) -> bool:
    return e.sort() == _REAL


def _to_real(e: z3.ExprRef) -> z3.ExprRef:
    return e if _is_real(e) else z3.ToReal(e)


def _to_int(e: z3.ExprRef) -> z3.ExprRef:
    return z3.ToInt(e) if _is_real(e) else e


def _coerce(a: z3.ExprRef, b: z3.ExprRef) -> tuple[z3.ExprRef, z3.ExprRef]:
    """Bring a numeric pair to a common z3 sort: if either is Real, promote both."""
    if a.sort() == b.sort():
        return a, b
    if _is_real(a) or _is_real(b):
        return _to_real(a), _to_real(b)
    return a, b


def _type_name(node) -> str | None:
    """Innermost C type name of a Decl/Typename node, e.g. 'int' or 'double'."""
    t = getattr(node, "type", None)
    while t is not None and not isinstance(t, c_ast.IdentifierType):
        t = getattr(t, "type", None)
    return t.names[-1] if isinstance(t, c_ast.IdentifierType) else None


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

    def add_constraint(self, cond: z3.ExprRef) -> SymState:
        return copy.replace(self, pc=self.pc + [z3.simplify(cond)])

    def set_var(self, name: str, val: z3.ExprRef) -> SymState:
        return copy.replace(self, env={**self.env, name: z3.simplify(val)})

    def with_exit(self, reason: Exit) -> SymState:
        return copy.replace(self, exit=reason)

    def inc_loop(self) -> SymState:
        return copy.replace(self, loop_depth=self.loop_depth + 1)

    def reset_exit(self) -> SymState:
        return copy.replace(self, exit=Exit.NORMAL)


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
        self._fresh_ctr = 0  # for naming fresh vars from modeled calls

        # Solver for feasibility (reused with push/pop)
        self.solver = z3.Solver()
        self.solver.set("timeout", self.SOLVER_TIMEOUT_MS)

        # Populated by _parse():
        self.mainq_params: list[tuple[str, str]] = []   # [(name, type), ...]
        self.vtrace_params: dict[str, list[str]] = {}   # {func_name: [param_names]}
        self.func_bodies: dict[str, c_ast.Compound] = {}

    # ── public ───────────────────────────────────────────────────────

    def run(self) -> list[tuple[str, z3.BoolRef, z3.BoolRef]]:
        """
        Execute symbolically.

        Returns list of (loc, pc, slocal) tuples where pc and slocal are z3
        boolean expressions, consumed directly (in-process) by
        SymStatesMaker.merge() — no text serialization/parsing round-trip.
        """
        self._parse()
        init_state = self._make_init_state()
        self._exec_compound(self.func_bodies["mainQ"], [init_state])
        return self._z3_records()

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
        for name, typ in self.mainq_params:
            state.env[name] = (z3.Real(f"X_{name}")
                               if typ in ("double", "float")
                               else z3.Int(f"X_{name}"))
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

    def _model_call(self, node: c_ast.FuncCall,
                    state: SymState) -> tuple[z3.ExprRef, list[z3.ExprRef]] | None:
        """
        Model a pure helper/library call as a fresh symbolic value plus the
        path constraints that define it. Returns (value, constraints) or None
        if the call isn't modeled. Lets symex handle programs like knuth that
        call e.g. isqrt without inlining the helper's loop.
        """
        if not isinstance(node.name, c_ast.ID):
            return None
        fname = node.name.name
        args = node.args.exprs if node.args else []
        if fname == "isqrt" and len(args) == 1:
            x = self._eval_expr(args[0], state)
            s = z3.Int(self._fresh_name("isqrt"))
            # integer sqrt: s >= 0 and s*s <= x < (s+1)*(s+1)
            cons = [s >= 0, s * s <= x, (s + 1) * (s + 1) > x]
            return s, cons
        return None

    def _fresh_name(self, prefix: str) -> str:
        self._fresh_ctr += 1
        return f"_{prefix}_{self._fresh_ctr}"

    def _exec_decl(self,
                   node: c_ast.Decl,
                   states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            if isinstance(node.init, c_ast.FuncCall):
                modeled = self._model_call(node.init, state)
                if modeled is not None:
                    val, cons = modeled
                    ns = state
                    for c in cons:
                        ns = ns.add_constraint(c)
                    result.append(ns.set_var(node.name, val))
                    continue
            declared = _type_name(node)
            is_real_decl = declared in ("double", "float")
            if node.init is not None:
                val = self._eval_expr(node.init, state)
                # honor the declared type (e.g. `double x = a;` makes x real)
                if is_real_decl:
                    val = _to_real(val)
                elif declared in ("int", "long", "short", "char"):
                    val = _to_int(val)
            else:
                # Uninitialised — use a fresh symbolic var of the declared sort
                val = (z3.Real(f"_uninit_{node.name}") if is_real_decl
                       else z3.Int(f"_uninit_{node.name}"))
            result.append(state.set_var(node.name, val))
        return result

    def _exec_assign(self,
                     node: c_ast.Assignment,
                     states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            # modeled calls (e.g. s = isqrt(n)) add defining constraints
            if node.op == "=" and isinstance(node.rvalue, c_ast.FuncCall):
                modeled = self._model_call(node.rvalue, state)
                if modeled is not None:
                    val, cons = modeled
                    target = (node.lvalue.name
                              if isinstance(node.lvalue, c_ast.ID) else None)
                    ns = state
                    for c in cons:
                        ns = ns.add_constraint(c)
                    result.append(ns.set_var(target, val) if target else ns)
                    continue
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
            if node.type in ("double", "float"):
                # exact rational, e.g. "3.25" -> 13/4
                return z3.RealVal(node.value.rstrip("fF"))
            return z3.IntVal(int(node.value, 0))

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
            val = self._eval_expr(node.expr, state)
            tn = _type_name(node.to_type)
            if tn in ("double", "float"):
                return _to_real(val)
            if tn in ("int", "long", "short", "char"):
                return _to_int(val)
            return val

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
        # mixed int/real: promote to a common sort so z3 doesn't reject the op
        # (and so "/" becomes real division when either operand is real)
        if node.op != "%":
            lhs, rhs = _coerce(lhs, rhs)

        arith = {
            "+": op_module.add,
            "-": op_module.sub,
            "*": op_module.mul,
            "/": op_module.truediv,   # real division if reals, else integer
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

    # ── output ─────────────────────────────────────────────────────────

    def _z3_records(self) -> list[tuple[str, z3.BoolRef, z3.BoolRef]]:
        """
        Return list of (loc, pc, slocal) tuples of z3 boolean expressions.

        pc is the conjunction of the path-condition constraints (z3 True if
        unconstrained); slocal is the conjunction of `var == expr` equalities
        over the variables in the vtrace param list.
        """
        out = []
        for rec in self.records:
            eqs = []
            for name in rec.param_names:
                v = rec.env_snapshot.get(name)
                if v is None:
                    continue
                # the symstate var must match the value's sort (Real for doubles)
                var = z3.Real(name) if _is_real(v) else z3.Int(name)
                eqs.append(var == v)
            if not eqs:
                continue
            # Leave pc/slocal unsimplified: PathCond.expr and PCs.myexpr already
            # z3.simplify at the right granularity, and an eager per-record
            # simplify here produces a form z3 solves much slower downstream
            # (~4x in the eqt check phase on cohendiv).
            slocal = z3.And(eqs)
            pc = z3.And(rec.pc_snapshot)   # z3.And([]) is True
            out.append((rec.loc, pc, slocal))
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
