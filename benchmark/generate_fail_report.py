#!/usr/bin/env python3
"""
Generate fail.md documenting all benchmark runs that failed or timed out.
Supports both campaign_full_791 and campaign_extended_111 formats.
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CAMPAIGN = REPO_ROOT / "benchmark/results/campaign_extended_111"

def generate_fail_report(campaign_dir: Path):
    manifest_path = campaign_dir / "manifest.json"
    assert manifest_path.is_file(), f"Missing {manifest_path}"

    with open(manifest_path, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    runs = manifest["runs"]
    git_commit = manifest.get("git_commit", manifest.get("metadata", {}).get("git_commit", "unknown"))
    timeout_sec = manifest.get("timeout_sec", manifest.get("metadata", {}).get("timeout_per_seed_sec", 120.0))
    total_runs = manifest.get("total_runs", manifest.get("metadata", {}).get("total_requested_runs", len(runs)))
    total_programs = manifest.get("total_programs", manifest.get("metadata", {}).get("total_benchmarks", len(set(r["program"] for r in runs))))

    # Filter non-success runs
    non_succ = [r for r in runs if r["outcome"] != "success"]

    # Group by suite
    by_suite = defaultdict(lambda: defaultdict(list))
    for r in non_succ:
        suite = r["suite"].upper()
        by_suite[suite][r["program"]].append(r)

    # Classify failure reasons
    reasons = defaultdict(int)
    for r in non_succ:
        reasons[r["outcome"]] += 1

    lines = []
    lines.append("# DIG-KN Evaluation Campaign: Failed & Timed-Out Benchmarks\n")
    lines.append(f"**Campaign Directory:** `{campaign_dir.relative_to(REPO_ROOT)}`  ")
    lines.append(f"**Git Commit:** `{git_commit}`  ")
    lines.append(f"**Timeout Budget:** {timeout_sec}s per seed  ")
    lines.append(f"**Depth Limit:** --se_maxdepth 16  ")
    lines.append(f"**Total Attempted Runs:** {total_runs} (across {total_programs} programs)  ")
    lines.append(f"**Total Failed / Timed-Out Runs:** {len(non_succ)} / {total_runs}  \n")

    lines.append("## 1. Summary by Suite\n")
    lines.append("| Suite | Total Programs | Programs with Failures/Timeouts | Total Failed Runs | Primary Failure Causes |")
    lines.append("| :--- | :---: | :---: | :---: | :--- |")

    suite_totals = {"NLA": 33, "NLA-MOSAIC": 14, "COMPLEXITY": 19, "HOLA": 45}

    for suite, pmap in sorted(by_suite.items()):
        total_p = suite_totals.get(suite, len(pmap))
        total_f_runs = sum(len(runs_list) for runs_list in pmap.values())
        cause_counts = defaultdict(int)
        for runs_list in pmap.values():
            for r in runs_list:
                cause_counts[r["outcome"]] += 1
        causes_str = ", ".join(f"{k}: {v}" for k, v in sorted(cause_counts.items(), key=lambda x: -x[1]))
        lines.append(f"| **{suite}** | {total_p} | {len(pmap)} | {total_f_runs} | {causes_str} |")

    lines.append("\n## 2. Failure Classification Breakdown\n")
    lines.append(f"- **`timeout`** ({reasons.get('timeout', 0)} runs): Execution exceeded the {timeout_sec}s per-seed timeout budget (primarily dense high-degree non-linear polynomial CEGIR iterations and nonlinear integer SMT solving).")
    lines.append(f"- **`depth_limit`** ({reasons.get('depth_limit', 0)} runs): Symbolic execution could not reach target trace locations within exploration depth (`--se_maxdepth 16`).")
    for k, v in sorted(reasons.items()):
        if k not in ("timeout", "depth_limit"):
            lines.append(f"- **`{k}`** ({v} runs): Non-zero exit code or exception during execution.")

    lines.append("\n## 3. Program-by-Program Failure Catalog\n")
    lines.append("| Suite | Program | Failed Runs / Total | Failure Outcomes | Sample Log File |")
    lines.append("| :--- | :--- | :---: | :--- | :--- |")

    # Sort by suite, program
    all_failed_progs = []
    for suite, pmap in sorted(by_suite.items()):
        for prog, runs_list in sorted(pmap.items()):
            all_failed_progs.append((suite, prog, runs_list))

    for suite, prog, runs_list in all_failed_progs:
        n_failed = len(runs_list)
        # outcome summary
        out_counts = defaultdict(int)
        for r in runs_list:
            out_counts[r["outcome"]] += 1
        out_str = ", ".join(f"{k} ({v}x)" for k, v in sorted(out_counts.items()))
        
        sample_log = runs_list[0].get("log_file", runs_list[0].get("log_path", ""))
        log_link = f"[`{sample_log}`]({sample_log})" if sample_log else "N/A"
        lines.append(f"| {suite} | `{prog}.c` | {n_failed}/7 | {out_str} | {log_link} |")

    lines.append("\n---\n")
    lines.append("### Diagnostic Notes & Recommended Resolutions\n")
    lines.append("1. **For `timeout` benchmarks:** Highly non-linear loops (e.g. `lcm2`, `knuth`, `prod4br`, `cohencu`, `fermat1`, `fermat2`) require higher degree templates ($d \\ge 4$) over 5+ variables, creating large SMT nonlinear integer formulas. Allocating higher solver budgets (`--rlimit` or timeout $> 300$s) or passing `--dosymba` helps mitigate solver stalls.")
    lines.append("2. **For `depth_limit` benchmarks:** Programs with multi-step postcondition placements after large fixed-bound loops (e.g. `30.dig.c` with 1000 iterations, `cav09_fig1a.c` with 100 iterations) require unrolling through the loop exit; placing trace markers inside the loop head allows synthesizing loop invariants directly without deep unrolling.")

    out_file = REPO_ROOT / "fail.md"
    with open(out_file, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Generated {out_file} with {len(non_succ)} failures across {len(all_failed_progs)} programs.")

if __name__ == "__main__":
    campaign = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_CAMPAIGN
    generate_fail_report(campaign)
