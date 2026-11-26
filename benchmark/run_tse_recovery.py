#!/usr/bin/env python3
"""Sequential, target-level rechecks of TSE successes missing in the campaign.

Examples:
  /usr/bin/python3 benchmark/run_tse_recovery.py --programs hola/11.dig hola/30.dig
  /usr/bin/python3 benchmark/run_tse_recovery.py --seeds 0 1 2 3 4 5 6
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
import fcntl
import hashlib
import itertools
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
import z3
import sympy
from analysis import Result
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--programs", nargs="+")
    parser.add_argument("--exclude", nargs="+", default=[],
                        help="programs to defer from this campaign")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0])
    parser.add_argument("--depth", type=int)
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--llm-provider", choices=("anthropic", "gemini", "groq"),
                        help="run the LLM proposal pipeline instead of algebraic inference")
    parser.add_argument("--llm-model", help="LLM model ID")
    parser.add_argument("--llm-rounds", type=int, default=3)
    parser.add_argument("--llm-no-traces", action="store_true")
    parser.add_argument("--profile", action="store_true", help="dump internal worker stacks every 30s")
    parser.add_argument("--stop-on-failure", action="store_true",
                        help="stop after the first unsuccessful target check")
    parser.add_argument("--reuse-results", type=Path,
                        help="recheck and reuse matching successful runs from this result tree")
    parser.add_argument("--out", type=Path, default=ROOT / "benchmark/results/tse_recovery/current")
    args = parser.parse_args()
    if args.llm_rounds < 1:
        parser.error("--llm-rounds must be positive")
    if args.llm_provider and args.reuse_results:
        parser.error("LLM campaigns cannot reuse algebraic results")
    if not args.llm_provider and (args.llm_model or args.llm_no_traces):
        parser.error("LLM settings require --llm-provider")
    if args.llm_provider and args.out == ROOT / "benchmark/results/tse_recovery/current":
        args.out = ROOT / "benchmark/results/llm" / time.strftime("%Y%m%d_%H%M%S")
    specs = json.loads((ROOT / "benchmark/tse_recovery_targets.json").read_text())
    programs = [name for name in (args.programs or list(specs))
                if name not in args.exclude]
    for name in args.exclude:
        if name not in specs:
            parser.error(f"unknown excluded program: {name}")
    for name in programs:
        if name not in specs or not specs[name]["targets"]:
            parser.error(f"unknown program or missing targets: {name}")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    # All invocations of this runner share one lock, irrespective of --out.
    lock = (ROOT / "benchmark/results/.tse_recovery.lock").open("w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        parser.error("another TSE recovery runner is already active")
    sources = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
               for p in (ROOT / "src").rglob("*.py")}
    manifest = {"types": "eqt,ieq,minmax,array,recurrence", "outer_concurrency": 1,
                "source_sha256": sources, "python_version": sys.version,
                "z3_version": z3.get_version_string(), "runs": []}
    if args.llm_provider:
        from llm_backend import DEFAULT_MODELS
        manifest["llm"] = {"provider": args.llm_provider,
                           "model": args.llm_model or DEFAULT_MODELS[args.llm_provider],
                           "max_rounds": args.llm_rounds, "no_traces": args.llm_no_traces}
    (out / "manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")
    reusable = {}
    if args.reuse_results:
        from generate_tse_recovery_report import collect
        reusable, _ = collect(specs, args.reuse_results.resolve())
    for seed in args.seeds:
        for name in programs:
            spec = specs[name]
            depth = args.depth or spec["depth"]
            previous = reusable.get((name, seed))
            if previous and previous.get("target_success") and previous["depth"] == depth:
                command = previous["command"]

                def argument(flag):
                    return command[command.index(flag)+1] if flag in command else None

                options = {"maxdeg": "maxdeg", "inpMaxV": "inpMaxV", "ideg": "ideg",
                           "iterms": "iterms", "icoefs": "icoefs"}
                matches = (argument("-types") == manifest["types"]
                           and all(argument("-"+flag) == (str(spec[key]) if key in spec else None)
                                   for key, flag in options.items()))
                if matches:
                    result = Result.load(Path(previous["result"]).parent)
                    checks = check_targets(result, spec["targets"])
                    if all(c["outcome"] == "recovered" for c in checks):
                        row = dict(previous, targets=checks, reused=True)
                        manifest["runs"].append(row)
                        (out / "manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")
                        print(f"{name} seed={seed}: reused matching run, targets=True", flush=True)
                        continue
            dest = out / name / f"seed_{seed}"
            dest.mkdir(parents=True, exist_ok=True)
            cmd = [sys.executable, "-u", "-O", str(ROOT / "src/dig.py"),
                   str(ROOT / spec["source"]), "--se_maxdepth", str(depth),
                   "-seed", str(seed), "-types", manifest["types"], "-tmpdir", str(dest)]
            if args.llm_provider:
                cmd.extend(["-llm", "-llm_provider", args.llm_provider,
                            "-llm_model", manifest["llm"]["model"],
                            "-llm_rounds", str(args.llm_rounds)])
                if args.llm_no_traces:
                    cmd.append("-llm_no_traces")
            if "maxdeg" in spec:
                cmd.extend(["-maxdeg", str(spec["maxdeg"])])
            for option in ("inpMaxV", "ideg", "iterms", "icoefs"):
                if option in spec:
                    cmd.extend(["-"+option, str(spec[option])])
            if args.profile:
                cmd[3] = str(ROOT / "benchmark/dig_profile.py")
            while True:
                before = set(dest.glob("Dig_*/result"))
                run_sources = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in (ROOT / "src").rglob("*.py")}
                started = time.monotonic()
                with (dest / "run.log").open("w") as log:
                    run_env = os.environ.copy()
                    if args.llm_provider == "groq":
                        run_env["DIG_GROQ_RATE_STATE"] = str(out / "groq_rate_state.json")
                    process = subprocess.Popen(cmd, cwd=ROOT, stdout=log,
                                               stderr=subprocess.STDOUT, start_new_session=True,
                                               env=run_env)
                    try:
                        returncode = process.wait(timeout=args.timeout)
                        outcome = "completed" if returncode == 0 else "error"
                    except subprocess.TimeoutExpired:
                        os.killpg(process.pid, signal.SIGKILL)
                        returncode = process.wait()
                        outcome = "timeout"
                    finally:
                        if process.poll() is None:
                            os.killpg(process.pid, signal.SIGKILL)
                            process.wait()
                row = {"program": name, "seed": seed, "depth": depth, "command": cmd,
                       "elapsed": round(time.monotonic()-started, 3), "returncode": returncode,
                       "outcome": outcome, "log": str(dest / "run.log")}
                row["source_sha256"] = run_sources
                row["benchmark_sha256"] = hashlib.sha256((ROOT / spec["source"]).read_bytes()).hexdigest()
                if args.llm_provider:
                    row["llm_evidence"] = [str(p) for p in dest.glob("Dig_*/llm_evidence.json")]
                if args.llm_provider and outcome == "error":
                    api_error = any(round_.get("api_error")
                                    for path in row["llm_evidence"]
                                    for round_ in json.loads(Path(path).read_text()).get("rounds", []))
                    if api_error:
                        details = [round_.get("api_error_metadata", {})
                                   for path in row["llm_evidence"]
                                   for round_ in json.loads(Path(path).read_text()).get("rounds", [])
                                   if round_.get("api_error")]
                        quota = next((d for d in details if d.get("http_status") == 429), {})
                        retry_sec = quota.get("retry_after")
                        if args.llm_provider == "groq" and retry_sec is not None:
                            try:
                                wait = max(30, float(retry_sec) + 5)
                            except ValueError:
                                wait = 60
                            if wait <= 600:
                                statefile = out / "groq_rate_state.json"
                                state = json.loads(statefile.read_text()) if statefile.exists() else {
                                    "timestamp": time.time(), "limits": {}}
                                state["blocked_until"] = time.time()+wait
                                statefile.write_text(json.dumps(state)+"\n")
                                print(f"{name} rate-limited; waiting {wait}s for rate quota reset before retrying...", flush=True)
                                time.sleep(wait)
                                continue
                        print("Stopping LLM campaign after an API error; inspect run.log before retrying.", flush=True)
                        return 1
                break
            created = set(dest.glob("Dig_*/result")) - before
            if outcome == "completed" and len(created) == 1:
                resultfile = created.pop()
                result = Result.load(resultfile.parent)
                row["result"] = str(resultfile)
                row["targets"] = check_targets(result, spec["targets"])
                row["invariant_status_counts"] = dict(Counter(
                    str(inv.stat) for invs in result.dinvs.values() for inv in invs))
                row["target_success"] = all(c["outcome"] == "recovered" for c in row["targets"])
            else:
                row["target_success"] = False
            manifest["runs"].append(row)
            (out / "manifest.json").write_text(json.dumps(manifest, indent=2)+"\n")
            print(f"{name} seed={seed} depth={depth}: {outcome}, "
                  f"targets={row['target_success']}, {row['elapsed']}s", flush=True)
            for target in row.get("targets", []):
                if target["outcome"] != "recovered":
                    print(f"  {target}", flush=True)
            if args.llm_provider and outcome == "error":
                api_error = any(round_.get("api_error")
                                for path in row["llm_evidence"]
                                for round_ in json.loads(Path(path).read_text()).get("rounds", []))
                if api_error:
                    details = [round_.get("api_error_metadata", {})
                               for path in row["llm_evidence"]
                               for round_ in json.loads(Path(path).read_text()).get("rounds", [])
                               if round_.get("api_error")]
                    quota = next((d for d in details if d.get("http_status") == 429), {})
                    retry_sec = quota.get("retry_after")
                    if args.llm_provider == "groq" and retry_sec is not None:
                        try:
                            wait = max(30, float(retry_sec) + 5)
                        except ValueError:
                            wait = 60
                        if wait <= 360:
                            statefile = out / "groq_rate_state.json"
                            state = json.loads(statefile.read_text()) if statefile.exists() else {
                                "timestamp": time.time(), "limits": {}}
                            state["blocked_until"] = time.time()+wait
                            statefile.write_text(json.dumps(state)+"\n")
                            print(f"Rate quota limit reached; waiting {wait}s for rate quota reset...", flush=True)
                            time.sleep(wait)
                            continue
                    print("Stopping LLM campaign after an API error; inspect run.log before retrying.", flush=True)
                    return 1
            if args.stop_on_failure and not row["target_success"]:
                return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
