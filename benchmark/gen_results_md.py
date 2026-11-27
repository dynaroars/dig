#!/usr/bin/env python3
"""Generate the canonical `results.md` status dashboard for DIG benchmarks.

Runs DIG strictly ONE PROGRAM AT A TIME (AGENTS.md: never run multiple `dig.py`
invocations concurrently; internal parallelism within a single run stays on).
Writes TSE-style summary tables per suite plus the full invariants discovered
at every `vtrace` location (and Lean 4 certification counts when enabled).

Usage:
    .venv/bin/python benchmark/gen_results_md.py
    .venv/bin/python benchmark/gen_results_md.py --suites nla NLA-mosaic complexity
    .venv/bin/python benchmark/gen_results_md.py --no-lean --suites nla complexity
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import signal
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PY = ROOT / ".venv" / "bin" / "python"
BENCH_ROOT = ROOT / "benchmark" / "c"
DEFAULT_SUITES = ("nla", "NLA-mosaic", "complexity")

_STAT_RE = re.compile(
    r"^\* prog \S+ locs (\d+); invs (\d+) \(([^)]*)\) "
    r"V (\d+) T (\d+) D (\d+); NL (\d+) \((\d+)\)",
    re.M,
)
_TIME_RE = re.compile(r"^-> time (.+)$", re.M)
_LOC_RE = re.compile(r"^(vtrace\w*)\s*\((\d+)\s+invs?\):$")


def _git_rev() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, text=True
        ).strip()
    except Exception:
        return "unknown"


def _parse_dig_output(out: str) -> dict:
    """Parse DIG's summary line, timing line, and per-location invariants."""
    info: dict = {
        "status": "fail",
        "locs": 0,
        "total": 0,
        "counts": {"Eqt": 0, "Oct": 0, "MMP": 0, "Congruence": 0},
        "V": 0,
        "T": 0,
        "D": 0,
        "NL": 0,
        "times": "",
        "invs_by_loc": {},
    }
    m = _STAT_RE.search(out)
    if m:
        info["status"] = "ok"
        info["locs"] = int(m.group(1))
        info["total"] = int(m.group(2))
        for part in m.group(3).split(","):
            part = part.strip()
            if ":" in part:
                k, v = part.split(":", 1)
                k = k.strip()
                if k in info["counts"]:
                    info["counts"][k] = int(v.strip())
        info["V"] = int(m.group(4))
        info["T"] = int(m.group(5))
        info["D"] = int(m.group(6))
        info["NL"] = int(m.group(7))
    tm = _TIME_RE.search(out)
    if tm:
        info["times"] = tm.group(1).strip()

    cur_loc: str | None = None
    for raw in out.splitlines():
        line = raw.strip()
        lm = _LOC_RE.match(line)
        if lm:
            cur_loc = lm.group(1)
            info["invs_by_loc"].setdefault(cur_loc, {})
            continue
        if cur_loc is not None:
            if not line or line.startswith(("lean-cert ", "certified ", "settings:", "alg:")):
                cur_loc = None
                continue
            if ":" in line:
                cat, rest = line.split(":", 1)
                cat = cat.strip()
                if cat in ("Eqt", "Oct", "MMP", "Congruence", "LLM"):
                    items = [x.strip() for x in rest.split(";") if x.strip()]
                    info["invs_by_loc"][cur_loc][cat] = items
    return info


def run_one(suite: str, cfile: Path, *, seed: int, timeout: int,
            certify_lean: bool) -> dict:
    if cfile.stem == "knuth":
        return {
            "suite": suite,
            "program": cfile.stem,
            "status": "skipped",
            "reason": "deferred per AGENTS.md",
            "wall_sec": 0.0,
        }
    with tempfile.TemporaryDirectory(prefix="digres_") as tmp:
        cmd = [str(PY), "-O", "dig.py", str(cfile.resolve()),
               "-seed", str(seed), "-tmpdir", tmp, "--z3-check"]
        if certify_lean:
            cmd.append("--certify-lean")
        t0 = time.monotonic()
        p = subprocess.Popen(
            cmd,
            cwd=ROOT / "src",
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        try:
            out, _ = p.communicate(timeout=timeout)
            rc: int | str = p.returncode
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.communicate()
            return {
                "suite": suite,
                "program": cfile.stem,
                "status": "timeout",
                "reason": f"timeout after {timeout}s",
                "wall_sec": round(time.monotonic() - t0, 1),
            }
        wall = round(time.monotonic() - t0, 1)
        parsed = _parse_dig_output(out)
        lean_rep = None
        runs = [d for d in Path(tmp).iterdir() if d.is_dir()]
        if runs and (runs[0] / "lean_certification.json").is_file():
            lean_rep = json.loads((runs[0] / "lean_certification.json").read_text())

    row = {
        "suite": suite,
        "program": cfile.stem,
        "returncode": rc,
        "wall_sec": wall,
        **parsed,
    }
    if lean_rep is not None:
        row["lean"] = {
            "status": lean_rep["status"],
            "certified": len(lean_rep.get("certified", [])),
            "dropped": len(lean_rep.get("dropped", [])),
            "unsupported": len(lean_rep.get("unsupported", [])),
            "lean_sec": round(lean_rep.get("lean_elapsed_sec", 0.0), 1),
            "certified_texts": [
                (c["loc"], c["text"]) for c in lean_rep.get("certified", [])
            ],
            "dropped_texts": [
                (c["loc"], c["text"]) for c in lean_rep.get("dropped", [])
            ],
            "unsupported_texts": [
                (c["loc"], c["text"]) for c in lean_rep.get("unsupported", [])
            ],
        }
    return row


def _canon_eqt_key(eqt_str: str) -> tuple[str, int, int]:
    """Return (sign-normalized key, degree, num_vars) for an 'lhs == rhs' string."""
    import sympy
    try:
        lhs, rhs = eqt_str.split("==", 1)
        names = set(re.findall(r"[A-Za-z_]\w*", eqt_str))
        loc = {n: sympy.Symbol(n) for n in names}
        expr = sympy.expand(sympy.sympify(lhs, locals=loc) - sympy.sympify(rhs, locals=loc))
        syms = sorted(expr.free_symbols, key=str)
        deg = sympy.Poly(expr, *syms).total_degree() if syms else 0
        terms = expr.as_ordered_terms()
        if terms and terms[0].as_coeff_Mul()[0] < 0:
            expr = -expr
        return str(expr), int(deg), len(syms)
    except Exception:
        return eqt_str.strip(), 1, 2


def _extract_equalities(r: dict) -> tuple[list[dict], list[dict]]:
    """Split a row's equalities into (featured, trivial), deduplicating sign flips.

    Featured = nonlinear (deg >= 2) or nontrivial linear (>= 2 variables).
    Trivial  = single-variable linear equalities like `q == 0` or `h == 0`.
    """
    cert_set = set()
    if r.get("lean"):
        cert_set = {tuple(x) for x in r["lean"].get("certified_texts", [])}

    featured: list[dict] = []
    trivial: list[dict] = []
    seen: set[tuple[str, str]] = set()
    for loc, cats in (r.get("invs_by_loc") or {}).items():
        for raw in cats.get("Eqt", []):
            key, deg, nvars = _canon_eqt_key(raw)
            if (loc, key) in seen:
                continue
            seen.add((loc, key))
            entry = {
                "loc": loc,
                "text": raw,
                "deg": deg,
                "nvars": nvars,
                "certified": (loc, raw) in cert_set,
            }
            if deg >= 2 or nvars >= 2:
                featured.append(entry)
            else:
                trivial.append(entry)
    # Sort featured: highest degree first, then loc, then text
    featured.sort(key=lambda e: (-e["deg"], e["loc"], e["text"]))
    return featured, trivial


def render_markdown(rows: list[dict], *, seed: int, certify_lean: bool,
                    suites: list[str]) -> str:
    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    rev = _git_rev()
    by_suite: dict[str, list[dict]] = {s: [] for s in suites}
    for r in rows:
        by_suite.setdefault(r["suite"], []).append(r)

    total_progs = len(rows)
    n_ok = sum(1 for r in rows if r["status"] == "ok")
    n_skip = sum(1 for r in rows if r["status"] == "skipped")
    n_fail = sum(1 for r in rows if r["status"] in ("fail", "timeout"))
    n_with_eqts = sum(1 for r in rows if r["status"] == "ok" and _extract_equalities(r)[0])

    lines = [
        "# DIG Benchmark Results",
        "",
        f"- **Updated:** {now} (commit `{rev}`)",
        f"- **Settings:** `-seed {seed} --z3-check`" + (" `--certify-lean`" if certify_lean else ""),
        f"- **Summary:** **{n_ok}/{total_progs - n_skip}** solved "
        f"(**{n_with_eqts}** with nontrivial/nonlinear equalities, "
        f"{n_fail} fail/timeout, {n_skip} skipped)",
        "",
        "> **Focus:** Tables highlight **nonlinear and nontrivial linear equalities** "
        "(≥ 2 variables or degree ≥ 2, sign-deduplicated). "
        "`✓` = **Lean 4 kernel-certified** (unbounded, zero Z3 in TCB); "
        "`○` = **inferred (Z3-checked), not Lean-verified**. "
        "**L** = locations, **V** = max vars, **NL(D)** = featured nonlinear eqts (max degree). "
        "Octagonal, min/max-plus, verified congruence, and trivial single-variable invariants "
        "are tucked into the collapsible details below each suite.",
        "",
    ]

    for suite in suites:
        srows = by_suite.get(suite, [])
        if not srows:
            continue
        ok_s = sum(1 for r in srows if r["status"] == "ok")
        eqt_s = sum(1 for r in srows if r["status"] == "ok" and _extract_equalities(r)[0])
        skip_s = sum(1 for r in srows if r["status"] == "skipped")
        lines.append(
            f"## Suite: `{suite}` ({ok_s}/{len(srows) - skip_s} ok, "
            f"{eqt_s} with nontrivial equalities)"
        )
        lines.append("")
        lines.append("| Prog | L | V | NL(D) | Time(s) | Status | Equalities (nonlinear & nontrivial linear) |")
        lines.append("|---|---:|---:|---:|---:|---|---|")

        for r in srows:
            prog = r["program"]
            if r["status"] != "ok":
                lines.append(f"| `{prog}` | - | - | - | {r['wall_sec']:.1f} | {r['status']} | - |")
                continue
            featured, _ = _extract_equalities(r)
            nl_cnt = sum(1 for e in featured if e["deg"] >= 2)
            max_d = max((e["deg"] for e in featured), default=0)
            nld = f"{nl_cnt}({max_d})" if featured else "0"
            if featured:
                multi_loc = len({e["loc"] for e in featured}) > 1
                parts = []
                for e in featured:
                    if certify_lean:
                        mark = " ✓" if e["certified"] else " ○"
                    else:
                        mark = ""
                    prefix = f"{e['loc']}: " if multi_loc else ""
                    parts.append(f"{prefix}`{e['text']}`{mark}")
                eqt_cell = "<br>".join(parts)
            else:
                eqt_cell = "*(none)*"
            lines.append(
                f"| `{prog}` | {r['locs']} | {r['V']} | {nld} | "
                f"{r['wall_sec']:.1f} | ok | {eqt_cell} |"
            )

        lines.append("")
        lines.append(f"<details><summary><b>Other invariants (Oct, MMP, Congruence, trivial equalities) — {suite}</b></summary>")
        lines.append("")
        for r in srows:
            if r["status"] != "ok" or not r.get("invs_by_loc"):
                continue
            _, trivial = _extract_equalities(r)
            cert_set = set()
            if r.get("lean"):
                cert_set = {tuple(x) for x in r["lean"].get("certified_texts", [])}
            other_lines = []
            for loc, cats in r["invs_by_loc"].items():
                triv_at_loc = [e["text"] for e in trivial if e["loc"] == loc]
                sub = []
                if triv_at_loc:
                    sub.append("**Trivial Eqt:** " + "; ".join(
                        f"`{x}`{' ✓' if (loc, x) in cert_set else ''}" for x in triv_at_loc))
                for cat in ("Congruence", "Oct", "MMP", "LLM"):
                    items = cats.get(cat, [])
                    if cat == "Congruence" and certify_lean:
                        # Show only Lean-verified congruences; unverified ones are omitted.
                        items = [x for x in items if (loc, x) in cert_set]
                    if items:
                        sub.append(f"**{cat}:** " + "; ".join(
                            f"`{x}`{' ✓' if (loc, x) in cert_set else (' ○' if certify_lean else '')}"
                            for x in items))
                if sub:
                    other_lines.append(f"  - `{loc}`: " + " | ".join(sub))
            if other_lines:
                lines.append(f"- **`{r['program']}`**")
                lines.extend(other_lines)
        lines.append("")
        lines.append("</details>")
        lines.append("")

    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--suites", nargs="+", default=list(DEFAULT_SUITES),
                    help="benchmark/c/<suite> directories to run")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--timeout", type=int, default=300, help="per-program timeout (s)")
    ap.add_argument("--no-lean", action="store_true", help="skip --certify-lean")
    ap.add_argument("--include-knuth", action="store_true")
    ap.add_argument("--render-only", action="store_true",
                    help="re-render results.md from existing --json-out without running DIG")
    ap.add_argument("--out", type=Path, default=ROOT / "results.md")
    ap.add_argument("--json-out", type=Path,
                    default=ROOT / "benchmark" / "results" / "results.json")
    args = ap.parse_args()

    certify_lean = not args.no_lean
    if args.render_only:
        rows = json.loads(args.json_out.read_text())
        suites = list(dict.fromkeys(r["suite"] for r in rows))
        args.out.write_text(render_markdown(
            rows, seed=args.seed, certify_lean=certify_lean, suites=suites
        ))
        print(f"Re-rendered {args.out} from {args.json_out}", flush=True)
        return 0
    rows: list[dict] = []
    args.json_out.parent.mkdir(parents=True, exist_ok=True)

    for suite in args.suites:
        sdir = BENCH_ROOT / suite
        if not sdir.is_dir():
            print(f"[warn] suite dir not found: {sdir}", flush=True)
            continue
        for cfile in sorted(sdir.glob("*.c")):
            if cfile.stem == "knuth" and not args.include_knuth:
                row = {
                    "suite": suite,
                    "program": cfile.stem,
                    "status": "skipped",
                    "reason": "deferred per AGENTS.md",
                    "wall_sec": 0.0,
                }
            else:
                print(f"=== [{suite}] {cfile.name} ===", flush=True)
                row = run_one(suite, cfile, seed=args.seed,
                              timeout=args.timeout, certify_lean=certify_lean)
                print(f"    status={row['status']} invs={row.get('total', 0)} "
                      f"wall={row['wall_sec']}s", flush=True)
            rows.append(row)
            args.json_out.write_text(json.dumps(rows, indent=2) + "\n")
            args.out.write_text(render_markdown(
                rows, seed=args.seed, certify_lean=certify_lean, suites=args.suites
            ))

    print(f"Wrote {args.out} and {args.json_out}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
