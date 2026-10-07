"""Exact semantic checks for the limited parameter experiments."""
import ast
import itertools
from pathlib import Path
import sys
import sympy
import z3

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from helpers.z3utils import Z3
from c_instrument import PrintTypeVisitor
from data.prog import Src
from data.symex_c import _preprocess
from pycparser import c_parser

def polynomial_consequence(invs, expression):
    """Prove equality implication by exact polynomial division when possible.

    A zero remainder certifies a combination of output equalities. A nonzero
    remainder supplies no verdict; it is not a counterexample. Approximate
    coefficients are left to the SMT check.
    """
    node = ast.parse(expression, mode="eval").body
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)):
        return False
    equations = [inv.inv.lhs-inv.inv.rhs for inv in invs
                 if isinstance(inv.inv, sympy.Equality)]
    if not equations:
        return False
    symbols = {str(s): s for eq in equations for s in eq.free_symbols}
    symbols.update({n.id: symbols.get(n.id, sympy.Symbol(n.id))
                    for n in ast.walk(node) if isinstance(n, ast.Name)})
    target = (sympy.sympify(ast.unparse(node.left), locals=symbols)
              - sympy.sympify(ast.unparse(node.comparators[0]), locals=symbols))
    polynomials = [target, *equations]
    if any(p.atoms(sympy.Float) for p in polynomials):
        return False
    generators = sorted({s for p in polynomials for s in p.free_symbols}, key=str)
    if not generators:
        return target == 0
    try:
        # A fitted basis may encode a target through cancellation between
        # generators. Polynomial division by the raw list can miss even a
        # constant-coefficient combination (e.g. the PLDI fig. 2 quartics).
        # Row reduction over QQ certifies those combinations exactly without
        # requiring an expensive Groebner-basis computation.
        dictionaries = [sympy.Poly(p, *generators, domain=sympy.QQ).as_dict()
                        for p in [*equations, target]]
        monomials = sorted(set().union(*(d.keys() for d in dictionaries)))
        basis, pivots = sympy.Matrix([
            [d.get(m, 0) for m in monomials] for d in dictionaries[:-1]]).rref()
        residual = sympy.Matrix([[dictionaries[-1].get(m, 0) for m in monomials]])
        for row, pivot in enumerate(pivots):
            residual -= residual[pivot] * basis.row(row)
        if not any(residual):
            return True
        _, remainder = sympy.reduced(target, sorted(equations, key=sympy.count_ops),
                                     *generators, domain=sympy.QQ)
    except (sympy.PolynomialError, ValueError):
        return False
    return remainder == 0


def check_targets(result, targets):
    """Check output implication, distinct from unbounded program verification."""
    visitor = PrintTypeVisitor("vtrace", "mainQ")
    visitor.visit(c_parser.CParser().parse(_preprocess(Path(result.filename).read_text())))
    inputs, declarations, _ = Src.parse_type_info("\n".join(visitor.typ_info))
    Z3.set_real_vars(s.name for ss in [inputs, *declarations.values()]
                     for s in ss if s.typ in ("D", "F"))
    checks = []
    for target in targets:
        loc, expression = target["location"], target["expression"]
        invs = result.dinvs.get(loc, [])
        outcome = "missing_location"
        if invs:
            solver = z3.Solver()
            solver.set(rlimit=1_000_000)
            solver.add(*[inv.expr for inv in invs])
            # An actual collected trace is an inexpensive satisfiability
            # witness for nonlinear output. Avoid making a hard unconstrained
            # model search a prerequisite for checking a literal equality.
            consistency = z3.unknown
            for trace in itertools.islice(result.dtraces.get(loc, []), 4):
                solver.push()
                solver.add(*[Z3.parse(name) == z3.RealVal(str(value))
                             for name, value in zip(trace.ss, trace.vs)])
                consistency = solver.check()
                solver.pop()
                if consistency == z3.sat:
                    break
            if consistency != z3.sat:
                consistency = solver.check()
            if consistency == z3.sat:
                if polynomial_consequence(invs, expression):
                    outcome = "recovered"
                else:
                    solver.add(z3.Not(Z3.parse(expression)))
                    verdict = solver.check()
                    outcome = ("recovered" if verdict == z3.unsat else
                               "missing" if verdict == z3.sat else "unknown")
            else:
                outcome = "inconsistent" if consistency == z3.unsat else "unknown"
        checks.append({**target, "outcome": outcome})
    return checks
