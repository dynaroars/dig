#!/usr/bin/env python3
"""Compile/validate NLA-mosaic, run DIG, and retain commands and complete logs."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction
import itertools
import json
import os
from pathlib import Path
import random
import re
import shlex
import signal
import subprocess
import sys
import tempfile
import time

import sympy

SUITE = Path(__file__).resolve().parent
ROOT = SUITE.parents[2]
sys.path.insert(0, str(ROOT / "src"))


def expression(text):
    names = set(re.findall(r"[A-Za-z_]\w*", text))
    return sympy.expand(sympy.sympify(text, locals={n: sympy.Symbol(n) for n in names}))


def equivalent(left, right):
    symbols = sorted(left.free_symbols | right.free_symbols, key=str)
    if not symbols:
        return left == right
    return sympy.Poly(left, *symbols).monic() == sympy.Poly(right, *symbols).monic()


def cases(spec):
    ranges = spec["input_ranges"]
    # Exhaust short one-parameter ranges; cover extremes and varied multi-input runs.
    if len(ranges) == 1:
        return [(i,) for i in range(ranges[0][0], ranges[0][1]+1)]
    values = {(tuple(v)) for v in itertools.product(*[
        sorted({lo, hi, (lo+hi)//2}) for lo, hi in ranges])}
    rng = random.Random(42)
    for _ in range(40):
        values.add(tuple(rng.randint(lo, hi) for lo, hi in ranges))
    # Exercise all short base-3 paths at the maximum iteration count.
    if spec["name"] in {"berggren", "continued_fraction", "continued_fraction_sign"}:
        values.update((ranges[0][1], path) for path in range(27))
    # Exhaust all initial seeds for the two three-dimensional polynomial maps.
    if spec["name"] in {"nagata", "fibonacci_trace"}:
        values.update((ranges[0][1], *seed) for seed in itertools.product(range(-2, 3), repeat=3))
    return sorted(values)


def validate(spec, tracefile=None):
    from c_instrument import instrument

    with tempfile.TemporaryDirectory(prefix="nla-mosaic-validate-", dir="/tmp") as scratch:
        scratch = Path(scratch)
        src, exe = scratch / "trace.c", scratch / "trace"
        declarations = instrument(SUITE / (spec["name"]+".c"), src)
        fields = next(line.split(";")[1:] for line in declarations if line.startswith("vtrace1;"))
        fields = [field.strip().split() for field in fields]
        cmd = ["gcc", "-std=c11", "-O1", "-Wall", "-Wextra", "-Werror",
               "-Wno-unused-parameter", "-fsanitize=undefined", "-fno-sanitize-recover=undefined",
               str(src), "-o", str(exe)]
        subprocess.run(cmd, check=True, capture_output=True, text=True)
        expected = [expression(t) for t in spec["expected"]]
        count = 0
        nonzero = [0]*len(expected)
        max_error = [0.0]*len(expected)
        inputs = cases(spec)
        rows = []
        for inp in inputs:
            cp = subprocess.run([str(exe), *map(str, inp)], check=True,
                                capture_output=True, text=True, timeout=2)
            for line in cp.stdout.splitlines():
                parts = [p.strip() for p in line.split(";")]
                if parts[0] != "vtrace1":
                    continue
                rows.append(line)
                assert len(parts[1:]) == len(fields), line
                vals = {sympy.Symbol(name): (sympy.Rational(Fraction(float(v))) if typ == "D"
                                            else sympy.Integer(v))
                        for (typ, name), v in zip(fields, parts[1:])}
                for idx, invariant in enumerate(expected):
                    residual = invariant.xreplace(vals)
                    if residual != 0:
                        nonzero[idx] += 1
                        max_error[idx] = max(max_error[idx], abs(float(residual)))
                        if spec["name"] != "welford":
                            raise ValueError(f"{spec['name']}: invariant failed on {inp}: {line}: {residual}")
                count += 1
        assert count > 0
        if tracefile is not None:
            header = next(line for line in declarations if line.startswith("vtrace1;"))
            tracefile.write_text(header+"\n"+"\n".join(rows)+"\n")
        return {"input_cases": len(inputs), "trace_rows": count, "ubsan": "passed",
                "nonzero_residual_rows": nonzero, "max_absolute_residual": max_error}


def run_one(spec, args):
    name = spec["name"]
    log = args.output / (name+".log")
    input_file = args.output / (name+".csv") if args.traces else SUITE / (name+".c")
    cmd = [sys.executable, "-O", str(ROOT / "src/dig.py"), str(input_file),
           "-types", args.types, "-maxdeg", str(spec["degree"]), "-seed", str(args.seed),
           "-nomp", "-tmpdir", "/tmp", "-log_level", "3"]
    if args.kapur:
        cmd.append("-dokapur")
    if args.input_max is not None:
        cmd.extend(["-inpMaxV", str(args.input_max)])
    if args.dynamic:
        cmd.extend(["-noss", "-nrandinps", "100"])
    start = time.perf_counter()
    env = dict(os.environ, PYTHONHASHSEED="0")
    timed_out = False
    with log.open("w") as stream:
        stream.write("# "+shlex.join(cmd)+"\n")
        stream.flush()
        proc = subprocess.Popen(cmd, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                start_new_session=True, env=env)
        try:
            proc.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait()
    elapsed = round(time.perf_counter()-start, 3)
    out = log.read_text()
    found = []
    # Use final CLI output only; debug proposals must not count as recovered.
    final = out.rsplit("\nrand seed ", 1)[-1] if "\nrand seed " in out else (
        out.rsplit("\nvtrace1 (", 1)[-1] if args.traces else "")
    for line in final.splitlines():
        if line.strip().startswith("Eqt:"):
            for text in line.strip()[4:].split(";"):
                if "==" in text:
                    left, right = text.strip().split("==", 1)
                    found.append(expression(left)-expression(right))
    matched = [any(equivalent(expression(e), inv) for inv in found) for e in spec["expected"]]
    summary = re.search(r"^\* prog .*?invs (\d+)", out, re.M)
    status = ("timeout" if timed_out else "error" if proc.returncode != 0
              else "ok" if summary or (args.dynamic or args.traces) and found else "no_summary")
    return {"name": name, "status": status, "elapsed_seconds": elapsed,
            "degree": spec["degree"], "expected": spec["expected"],
            "expected_found": matched, "equalities": list(map(str, found)),
            "invariant_count": int(summary.group(1)) if summary else len(found),
            "returncode": proc.returncode, "command": cmd,
            "log": log.name}


def report(rows, args, validation):
    config = {"seed": args.seed, "timeout_seconds": args.timeout, "jobs": args.jobs,
              "types": args.types, "kapur": args.kapur, "dynamic": args.dynamic,
              "input_max": args.input_max,
              "trace_mode": args.traces,
              "python": sys.version, "platform": sys.platform}
    (args.output / "results.json").write_text(json.dumps(
        {"configuration": config, "validation": validation, "runs": rows}, indent=2)+"\n")
    lines = ["# NLA-mosaic DIG results", "",
             f"Seed {args.seed}; {args.timeout}s per program; `{args.types}`; "
             f"explicit degree caps from manifest; Kapur={args.kapur}; dynamic={args.dynamic}; "
             f"trace input={args.traces}.", "",
             "Recovery means the target equality is present up to a nonzero scalar factor. "
             "Counts alone are not a recovery criterion. DIG's ordinary equality checking "
             "uses bounded symbolic states; these results do not establish unbounded proofs.", "",
             "| Program | Run status | Seconds | Target equalities recovered | All invariants |",
             "|---|---|---:|---:|---:|"]
    for row in rows:
        lines.append(f"| [{row['name']}]({row['name']}.log) | {row['status']} | "
                     f"{row['elapsed_seconds']:.3f} | {sum(row['expected_found'])}/"
                     f"{len(row['expected'])} | {row['invariant_count']} |")
    lines.extend(["", "## Equality output", ""])
    for row in rows:
        lines.extend([f"### {row['name']}", "", "```text",
                      *row["equalities"], "```", ""])
    if validation:
        lines.extend(["## Concrete C validation", "",
                      "Compiled instrumented programs with GCC warnings as errors and UBSan. "
                      "Checked the expected polynomial on every captured trace using exact "
                      "integers and the exact rationals represented by C doubles.", "",
                      "| Program | Input cases | Trace rows | Nonzero residual rows per target |",
                      "|---|---:|---:|---|"])
        for name, val in sorted(validation.items()):
            lines.append(f"| {name} | {val['input_cases']} | {val['trace_rows']} | "
                         f"{val['nonzero_residual_rows']} |")
        lines.extend(["", "Welford specifies exact-real invariants; nonzero residuals in its "
                      "C double traces expose rounding and are recorded in results.json.", ""])
    (args.output / "RESULTS.md").write_text("\n".join(lines)+"\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", nargs="+", help="program stems to run")
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--types", default="eqt,recurrence")
    parser.add_argument("--kapur", action="store_true")
    parser.add_argument("--dynamic", action="store_true")
    parser.add_argument("--traces", action="store_true", help="infer from validated C trace CSVs")
    parser.add_argument("--input-max", type=int, help="DIG random-input sampling upper bound")
    parser.add_argument("--skip-validation", action="store_true")
    parser.add_argument("--output", type=Path, default=SUITE / "results" / "baseline")
    args = parser.parse_args()
    if args.jobs < 1 or args.timeout <= 0:
        parser.error("jobs and timeout must be positive")
    if args.traces and (args.skip_validation or args.dynamic or args.kapur):
        parser.error("--traces requires validation and cannot be combined with --dynamic/--kapur")
    specs = json.loads((SUITE / "manifest.json").read_text())["programs"]
    if args.only:
        unknown = set(args.only)-{s["name"] for s in specs}
        if unknown:
            parser.error(f"unknown programs: {sorted(unknown)}")
        specs = [s for s in specs if s["name"] in args.only]
    args.output = args.output.resolve()
    # Reports/log links live below the suite, so keep outputs there.
    if not args.output.is_relative_to(SUITE):
        parser.error("output must be inside NLA-mosaic")
    args.output.mkdir(parents=True, exist_ok=True)
    validation = {}
    if not args.skip_validation:
        for spec in specs:
            csvfile = args.output / (spec["name"]+".csv") if args.traces else None
            validation[spec["name"]] = validate(spec, csvfile)
            print("validated", spec["name"], validation[spec["name"]], flush=True)
    rows = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        pending = {pool.submit(run_one, spec, args): spec for spec in specs}
        for future in as_completed(pending):
            row = future.result()
            rows.append(row)
            rows.sort(key=lambda r: r["name"])
            report(rows, args, validation)
            print(row["name"], row["status"], row["elapsed_seconds"],
                  "targets", row["expected_found"], flush=True)
    report(rows, args, validation)


if __name__ == "__main__":
    main()
