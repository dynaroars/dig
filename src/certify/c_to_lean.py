"""Translate a DIG C benchmark's `mainQ` into a Lean `DigCert.Stmt State`.

This printer is in the trusted base: the certificate proves `Safe prog` for
the `prog` printed here, so the translation must mirror C semantics for the
supported subset. Anything outside the subset raises `Unsupported`.

Supported subset (mathematical integers; C overflow is out of scope):
  * scalar integer parameters/locals (`int`, `long`, `short`, `char`,
    signed variants); no globals, pointers, arrays, structs, floats,
    unsigned types, or shadowing re-declarations;
  * side-effect-free expressions over + - * / % (C truncating division as
    `cdiv`/`cmod`, each preceded by a `d ≠ 0` check), unary -, casts to
    integer types, ternary `?:`, comparisons, && || !;
  * statements: declarations (uninitialised → havoc), `=`, `op=`, `++`/`--`,
    if/else, while, for, break, continue, return, blocks, empty statements;
  * calls: `vassume(c)` → assume, `vtrace*(args)` → per-invariant checks,
    `x = unknown()/nondet*()` → havoc.
"""

import re
from dataclasses import dataclass, field
from pathlib import Path
from collections.abc import Callable

from pycparser import c_ast, c_parser

INT_TYPES = {"int", "long", "short", "char", "signed"}
NONDET_RE = re.compile(r"^(unknown|nondet)(_\w*)?$|^__VERIFIER_nondet_\w+$")


class Unsupported(Exception):
    pass


def field_name(c_name: str) -> str:
    return f"v_{c_name}"


def _coord(n: c_ast.Node) -> str:
    c = getattr(n, "coord", None)
    return f"line {c.line}" if c else "?"


def _is_vtrace(name: str) -> bool:
    return name.startswith("vtrace")


@dataclass
class Loop:
    idx: int
    head_loc: str | None          # vtrace loc whose call is the body's first stmt
    guard: str                    # Lean Prop over `s`
    trivial_guard: bool           # while(1)
    writes: set[str] = field(default_factory=set)
    parent: int | None = None


@dataclass
class Site:
    """A vtrace call: invariant parameters are bound to these argument terms."""
    loc: str
    args: dict[str, str]          # param name -> Lean Int term over `s`
    loop: int | None              # enclosing loop (innermost), if any
    arg_vars: dict[str, set[str]] = field(default_factory=dict)  # param -> C vars


@dataclass
class Assume:
    """A top-level `vassume(c)`: a candidate frame fact for later loops."""
    cond: str                     # Lean Prop over `s`
    vars: set[str]


# Callbacks supplied by the emitter:
#   checks(site) -> list of (tag, Lean Prop over `s`) to assert at the site
#   head(loop)   -> list of (tag, Lean Prop over `s`) forming the loop invariant
ChecksFn = Callable[[Site], list[tuple[str, str]]]
HeadFn = Callable[[Loop], list[tuple[str, str]]]


def _ids(n: c_ast.Node) -> set[str]:
    out: set[str] = set()

    class V(c_ast.NodeVisitor):
        def visit_ID(v, x):
            out.add(x.name)

    V().visit(n)
    return out


def _type_names(t: c_ast.Node) -> list[str]:
    if isinstance(t, c_ast.TypeDecl) and isinstance(t.type, c_ast.IdentifierType):
        return list(t.type.names)
    raise Unsupported(f"non-scalar type at {_coord(t)}")


def _check_int_type(t: c_ast.Node, what: str) -> None:
    names = _type_names(t)
    if not names or not set(names) <= INT_TYPES:
        raise Unsupported(f"{what}: type {' '.join(names)} not supported")


class CProgram:
    """Parsed `mainQ` plus the information the emitter needs."""

    def __init__(self, cfile: Path | str):
        from data.symex_c import _preprocess   # strips includes/comments
        self.cfile = Path(cfile)
        ast = c_parser.CParser().parse(_preprocess(self.cfile.read_text()),
                                       self.cfile.name)
        self.vtrace_params: dict[str, list[str]] = {}
        main = None
        for node in ast.ext:
            if isinstance(node, c_ast.FuncDef):
                name = node.decl.name
                if name == "mainQ":
                    main = node
                elif _is_vtrace(name):
                    args = node.decl.type.args
                    self.vtrace_params[name] = (
                        [p.name for p in args.params] if args else [])
            elif isinstance(node, c_ast.Decl):
                if isinstance(node.type, c_ast.FuncDecl):    # prototype
                    if _is_vtrace(node.name) and node.name not in self.vtrace_params:
                        args = node.type.args
                        self.vtrace_params[node.name] = (
                            [p.name for p in args.params] if args else [])
                    continue
                raise Unsupported(f"global declaration {node.name}")
        if main is None:
            raise Unsupported("mainQ not found")
        self.main = main
        self.params: list[str] = []
        args = main.decl.type.args
        for p in (args.params if args else []):
            if isinstance(p, c_ast.Typename):      # (void)
                continue
            _check_int_type(p.type, f"parameter {p.name}")
            self.params.append(p.name)
        self.vars: list[str] = list(self.params)
        self._collect_decls(main.body)
        self.loops: list[Loop] = []
        self.sites: list[Site] = []
        self.assumes: list[Assume] = []
        self.use_frames = True
        # dry run: discover loops/sites and reject unsupported constructs
        self._checks: ChecksFn = lambda site: []
        self._head: HeadFn = lambda loop: []
        self.render_prog()

    # ── declarations ───────────────────────────────────────────────────
    def _collect_decls(self, body: c_ast.Node) -> None:
        seen = set(self.params)

        class V(c_ast.NodeVisitor):
            def visit_Decl(v, n):
                if isinstance(n.type, c_ast.FuncDecl):
                    raise Unsupported(f"local function declaration {n.name}")
                _check_int_type(n.type, f"variable {n.name}")
                if n.name in seen:
                    raise Unsupported(f"re-declaration/shadowing of {n.name}")
                seen.add(n.name)
                self.vars.append(n.name)

        V().visit(body)

    # ── expressions ───────────────────────────────────────────────────
    def _var(self, name: str) -> str:
        if name not in self.vars:
            raise Unsupported(f"unknown identifier {name}")
        return f"s.{field_name(name)}"

    def expr(self, n: c_ast.Node, divs: list[str]) -> str:
        """Lean `Int` term over `s`. Each division appends its nonzero-divisor
        obligation to `divs`, guarded by the short-circuit conditions under
        which C actually evaluates it (&&, ||, ?:)."""
        if isinstance(n, c_ast.Constant):
            if n.type not in ("int", "long", "long int", "long long int"):
                raise Unsupported(f"constant {n.value} of type {n.type}")
            v = n.value.rstrip("lL")
            if v.lower().endswith("u") or "u" in n.value.lower():
                raise Unsupported(f"unsigned constant {n.value}")
            iv = int(v, 0) if not (len(v) > 1 and v[0] == "0" and v.isdigit()) \
                else int(v, 8)
            return str(iv) if iv >= 0 else f"({iv})"
        if isinstance(n, c_ast.ID):
            return self._var(n.name)
        if isinstance(n, c_ast.UnaryOp):
            if n.op == "-":
                return f"(-{self.expr(n.expr, divs)})"
            if n.op == "+":
                return self.expr(n.expr, divs)
            raise Unsupported(f"unary {n.op} in integer expression at {_coord(n)}")
        if isinstance(n, c_ast.BinaryOp):
            if n.op in ("+", "-", "*"):
                return f"({self.expr(n.left, divs)} {n.op} {self.expr(n.right, divs)})"
            if n.op in ("/", "%"):
                a, b = self.expr(n.left, divs), self.expr(n.right, divs)
                divs.append(f"({b} ≠ 0)")
                fn = "cdiv" if n.op == "/" else "cmod"
                return f"({fn} {a} {b})"
            raise Unsupported(f"operator {n.op} in integer expression at {_coord(n)}")
        if isinstance(n, c_ast.Cast):
            _check_int_type(n.to_type.type, "cast")
            return self.expr(n.expr, divs)
        if isinstance(n, c_ast.TernaryOp):
            c = self.cond(n.cond, divs)
            td: list[str] = []
            ed: list[str] = []
            x, y = self.expr(n.iftrue, td), self.expr(n.iffalse, ed)
            divs += [f"({c} → {d})" for d in td]
            divs += [f"((¬ {c}) → {d})" for d in ed]
            return f"(if {c} then {x} else {y})"
        raise Unsupported(f"{type(n).__name__} expression at {_coord(n)}")

    REL = {"<": "<", "<=": "≤", ">": ">", ">=": "≥", "==": "=", "!=": "≠"}

    def cond(self, n: c_ast.Node, divs: list[str]) -> str:
        """Lean `Prop` over `s` (C truthiness: nonzero)."""
        if isinstance(n, c_ast.BinaryOp):
            if n.op in self.REL:
                return (f"({self.expr(n.left, divs)} {self.REL[n.op]} "
                        f"{self.expr(n.right, divs)})")
            if n.op in ("&&", "||"):
                a = self.cond(n.left, divs)
                rd: list[str] = []
                b = self.cond(n.right, rd)
                g = a if n.op == "&&" else f"(¬ {a})"   # when C evaluates rhs
                divs += [f"({g} → {d})" for d in rd]
                return f"({a} {'∧' if n.op == '&&' else '∨'} {b})"
        if isinstance(n, c_ast.UnaryOp) and n.op == "!":
            return f"(¬ {self.cond(n.expr, divs)})"
        if isinstance(n, c_ast.Constant) and n.type == "int":
            return "True" if int(n.value.rstrip("lL"), 0) != 0 else "False"
        return f"({self.expr(n, divs)} ≠ 0)"

    # ── statements ────────────────────────────────────────────────────
    @staticmethod
    def seq(stmts: list[str]) -> str:
        if not stmts:
            return ".skip"
        out = stmts[-1]
        for st in reversed(stmts[:-1]):
            out = f".seq ({st}) <|\n  {out}"
        return out

    @staticmethod
    def _assign(name: str, term: str) -> str:
        return f".assign fun s => {{ s with {field_name(name)} := {term} }}"

    @staticmethod
    def _havoc(name: str) -> str:
        return f".havocInt fun s n => {{ s with {field_name(name)} := n }}"

    @staticmethod
    def _div_checks(divs: list[str], where: c_ast.Node) -> list[str]:
        return [f'.check fun s => Tag "div@{_coord(where).split()[-1]}" {d}'
                for d in divs]

    def _is_nondet(self, n: c_ast.Node) -> bool:
        return (isinstance(n, c_ast.FuncCall) and isinstance(n.name, c_ast.ID)
                and bool(NONDET_RE.match(n.name.name)))

    def _assign_stmt(self, name: str, rhs: c_ast.Node | None, at: c_ast.Node,
                     writes: set[str]) -> list[str]:
        self._var(name)
        for lp in self._loop_stack:
            self.loops[lp].writes.add(name)
        if rhs is None or self._is_nondet(rhs):
            return [self._havoc(name)]
        divs: list[str] = []
        term = self.expr(rhs, divs)
        return self._div_checks(divs, at) + [self._assign(name, term)]

    def stmt(self, n: c_ast.Node | None) -> list[str]:
        if n is None or isinstance(n, c_ast.EmptyStatement):
            return []
        if isinstance(n, c_ast.Compound):
            out: list[str] = []
            for it in n.block_items or []:
                out += self.stmt(it)
            return out
        if isinstance(n, c_ast.Decl):
            return self._assign_stmt(n.name, n.init, n, set())
        if isinstance(n, c_ast.DeclList):
            out = []
            for d in n.decls:
                out += self.stmt(d)
            return out
        if isinstance(n, c_ast.Assignment):
            if not isinstance(n.lvalue, c_ast.ID):
                raise Unsupported(f"assignment to non-variable at {_coord(n)}")
            name = n.lvalue.name
            if n.op == "=":
                return self._assign_stmt(name, n.rvalue, n, set())
            op = n.op[:-1]
            if op not in ("+", "-", "*", "/", "%"):
                raise Unsupported(f"assignment operator {n.op} at {_coord(n)}")
            if self._is_nondet(n.rvalue):
                raise Unsupported(f"nondet in compound assignment at {_coord(n)}")
            rhs = c_ast.BinaryOp(op, c_ast.ID(name), n.rvalue, n.coord)
            return self._assign_stmt(name, rhs, n, set())
        if isinstance(n, c_ast.UnaryOp) and n.op in ("p++", "++", "p--", "--"):
            if not isinstance(n.expr, c_ast.ID):
                raise Unsupported(f"{n.op} on non-variable at {_coord(n)}")
            name = n.expr.name
            op = "+" if "++" in n.op else "-"
            rhs = c_ast.BinaryOp(op, c_ast.ID(name), c_ast.Constant("int", "1"),
                                 n.coord)
            return self._assign_stmt(name, rhs, n, set())
        if isinstance(n, c_ast.FuncCall):
            return self._call(n)
        if isinstance(n, c_ast.If):
            divs: list[str] = []
            c = self.cond(n.cond, divs)
            return self._div_checks(divs, n) + [
                f".ite (fun s => {c})\n  ({self.seq(self.stmt(n.iftrue))})\n"
                f"  ({self.seq(self.stmt(n.iffalse))})"]
        if isinstance(n, c_ast.While):
            return [self._loop(n.cond, n.stmt, None, n)]
        if isinstance(n, c_ast.For):
            init = self.stmt(n.init) if n.init is not None else []
            return init + [self._loop(n.cond, n.stmt, n.next, n)]
        if isinstance(n, c_ast.Break):
            return [".brk"]
        if isinstance(n, c_ast.Continue):
            return [".cont"]
        if isinstance(n, c_ast.Return):
            divs = []
            if n.expr is not None:            # validate; checks its divisions
                try:
                    self.expr(n.expr, divs)
                except Unsupported:
                    divs = []
                    self.cond(n.expr, divs)
            return self._div_checks(divs, n) + [".ret"]
        raise Unsupported(f"{type(n).__name__} statement at {_coord(n)}")

    def _call(self, n: c_ast.FuncCall) -> list[str]:
        if not isinstance(n.name, c_ast.ID):
            raise Unsupported(f"indirect call at {_coord(n)}")
        fname = n.name.name
        args = n.args.exprs if n.args else []
        if fname == "vassume":
            if len(args) != 1:
                raise Unsupported("vassume arity")
            divs: list[str] = []
            c = self.cond(args[0], divs)
            if self._discover and not self._loop_stack and not divs:
                self.assumes.append(Assume(c, _ids(args[0])))
            return self._div_checks(divs, n) + [f".assume fun s => {c}"]
        if _is_vtrace(fname):
            params = self.vtrace_params.get(fname)
            if params is None or len(params) != len(args):
                raise Unsupported(f"{fname}: unknown or arity mismatch")
            divs = []
            terms = {p: self.expr(a, divs) for p, a in zip(params, args)}
            if divs:
                raise Unsupported(f"{fname}: division in vtrace argument")
            site = Site(fname, terms,
                        self._loop_stack[-1] if self._loop_stack else None,
                        {p: _ids(a) for p, a in zip(params, args)})
            if self._discover:
                self.sites.append(site)
            return [f'.check fun s => Tag "{tag}" {prop}'
                    for tag, prop in self._checks(site)]
        raise Unsupported(f"call to {fname} at {_coord(n)}")

    def _loop(self, cond: c_ast.Node | None, body: c_ast.Node,
              nxt: c_ast.Node | None, at: c_ast.Node) -> str:
        divs: list[str] = []
        guard = "True" if cond is None else self.cond(cond, divs)
        if divs:
            raise Unsupported(f"division in loop guard at {_coord(at)}")
        trivial = guard == "True"
        head_loc = None
        items = body.block_items if isinstance(body, c_ast.Compound) else [body]
        first = items[0] if items else None
        if (isinstance(first, c_ast.FuncCall) and isinstance(first.name, c_ast.ID)
                and _is_vtrace(first.name.name)):
            head_loc = first.name.name
        if self._discover:
            idx = len(self.loops)
            self.loops.append(Loop(idx, head_loc, guard, trivial,
                                   parent=self._loop_stack[-1] if self._loop_stack else None))
        else:
            idx = self._loop_counter
        self._loop_counter += 1
        self._loop_stack.append(idx)
        try:
            body_stmts = self.stmt(body)
            next_stmts = self.stmt(nxt) if nxt is not None else []
        finally:
            self._loop_stack.pop()
        body_s = self.seq(body_stmts)
        if next_stmts:
            body_s = (f".seq (.catchCont ({body_s})) <|\n  "
                      f"{self.seq(next_stmts)}")
        conj = [f'Tag "{t}" {p}' for t, p in self._head(self.loops[idx])]
        inv = " ∧ ".join(conj) if conj else "True"
        frame = self._frame(self.loops[idx])
        return (f".loop (fun s => {inv})\n  (fun s => [{frame}])\n"
                f"  (fun s => {guard})\n  ({body_s})")

    def _frame(self, lp: Loop) -> str:
        """Fields the loop never writes. Lean proves the body preserves them,
        so an error here causes a failed VC, never an unsound certificate."""
        if self._discover or not self.use_frames:
            return ""
        return ", ".join(f"s.{field_name(v)}" for v in self.vars
                         if v not in lp.writes)

    # ── rendering ─────────────────────────────────────────────────────
    def render_prog(self, checks: ChecksFn | None = None,
                    head: HeadFn | None = None) -> str:
        self._discover = checks is None
        if checks is not None:
            self._checks, self._head = checks, head
        self._loop_stack: list[int] = []
        self._loop_counter = 0
        body = self.stmt(self.main.body)
        return self.seq(body + [".ret"])

    def render_state(self) -> str:
        fields = "\n".join(f"  {field_name(v)} : Int" for v in self.vars)
        return f"structure State where\n{fields}"
