#!/usr/bin/env python3
"""Record LLM campaign results and partial verification evidence; never run DIG."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT / "benchmark")]
from catalog_tse_invariants import catalog, render


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaigns", nargs="+", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    specs = json.loads((ROOT / "benchmark/tse_recovery_targets.json").read_text())
    programs = [p for p in specs if p != "nla/knuth"]
    rows, evidence, files, campaign_settings = [], {}, {}, []
    for directory in args.campaigns:
        manifest = directory / "manifest.json"
        data = json.loads(manifest.read_text())
        campaign_settings.append({"manifest": str(manifest), "llm": data["llm"],
                                  "source_sha256": data["source_sha256"]})
        rows.extend(data["runs"])
        for path in directory.rglob("*"):
            if path.is_file():
                files[str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
        for row in data["runs"]:
            rounds = []
            for name in row.get("llm_evidence", []):
                rounds.extend(json.loads(Path(name).read_text()).get("rounds", []))
            evidence[row["program"]] = rounds
    # Keep latest run per program if campaigns represent successive stages
    deduped_rows = {}
    for r in rows:
        deduped_rows[r["program"]] = r
    rows = [deduped_rows[p] for p in programs if p in deduped_rows]
    names = [r["program"] for r in rows]
    completed = [r for r in rows if r["outcome"] == "completed" and r.get("result")]
    recovered = [r for r in completed if r["target_success"]]
    usage = [rnd.get("usage", {}) for rounds in evidence.values() for rnd in rounds]
    summary = {
        "planned": len(programs), "attempted": len(rows), "completed": len(completed),
        "target_confirmed_programs": len(recovered),
        "completed_missing_some_targets": len(completed) - len(recovered),
        "errors": sum(r["outcome"] == "error" for r in rows),
        "timeouts": sum(r["outcome"] == "timeout" for r in rows),
        "pending": [p for p in programs if p not in names], "seed": 0,
        "proposal_responses": sum("response" in rnd for rounds in evidence.values() for rnd in rounds),
        "api_total_tokens": sum(u.get("total_tokens", 0) for u in usage),
        "settings": campaign_settings, "runs": rows,
        "partial_evidence": {r["program"]: evidence[r["program"]]
                             for r in rows if r["outcome"] != "completed"},
        "interpretation": "Target implication over saved output is separate from unbounded "
                          "program verification. Errors with partial evidence are not completed evaluations.",
    }
    (args.out / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    columns = ["program", "seed", "outcome", "elapsed", "target_success", "log", "result"]
    with (args.out / "programs.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    data = catalog(specs, {(r["program"], r["seed"]): r for r in rows})
    (args.out / "equalities.json").write_text(json.dumps(data, indent=2)+"\n")
    (args.out / "equalities.md").write_text(render(data))
    (args.out / "artifact_checksums.json").write_text(json.dumps(files, indent=2)+"\n")
    text = (f"# Groq seed-0 campaign\n\n"
            f"Attempted {len(rows)}/{len(programs)} programs; {len(completed)} completed; "
            f"{len(recovered)} recovered all listed targets. "
            f"Errors: {summary['errors']}; timeouts: {summary['timeouts']}.\n\n"
            "All programs are attempted once at seed 0 with serial outer execution. "
            "Knuth is deferred. API startup diagnostics are separate. Prompt/trace, response, "
            "token usage, candidate and verification records are in each llm_evidence.json. "
            "Partial evidence is retained for interrupted programs, without counting them as completed. "
            "Original commands, settings, code hashes and log paths are retained in summary.json.\n\n"
            "The initial two completed programs used a 4096-token output cap; later requests used "
            "1024 and then 512 with rate pacing after the account's separate output-token limit "
            "was identified. Per-response metadata and per-run source hashes identify these settings. "
            "Account quota waits are included in elapsed times. These are "
            "configured pilot timings, not a controlled speed comparison with the algebraic baseline. "
            "Interesting alternative/high-degree equalities are catalogued regardless of target success.\n\n"
            "Pending programs: " + (", ".join(summary["pending"]) or "none") + ".\n")
    (args.out / "README.md").write_text(text)
    print({k: summary[k] for k in ("planned", "attempted", "completed", "target_confirmed_programs", "errors", "timeouts", "api_total_tokens")})


if __name__ == "__main__":
    main()
