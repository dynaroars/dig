import os
import sys
import uuid
import json
import time
import shutil
import threading
import logging
from pathlib import Path
from flask import Flask, request, jsonify, send_from_directory
from flask_cors import CORS

from docker_runner import DIGRunner

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

DIG_ROOT = Path(os.environ.get("DIG_ROOT", Path(__file__).resolve().parent.parent))
EXAMPLES_DIR = Path(__file__).resolve().parent / "examples"
NLA_DIR = DIG_ROOT / "benchmark" / "c" / "nla"
SYMEX_DIR = DIG_ROOT / "tests" / "symex_progs"
CLASSIC_DIR = Path(__file__).resolve().parent

NLA_DESCRIPTIONS = {
    "ariths": "Built-in arithmetic functions (addition, multiplication).",
    "bresenham": "Bresenham line drawing algorithm.",
    "cohencu": "Cohen's cube computation (degree 3).",
    "cohendiv": "Cohen's integer division with nested loops.",
    "dijkstra": "Dijkstra's integer square root.",
    "divbin": "Binary (shift-based) integer division.",
    "egcd": "Extended Euclidean GCD (single loop).",
    "egcd2": "Extended Euclidean GCD (two nested loops).",
    "egcd3": "Extended Euclidean GCD (three nested loops).",
    "fermat1": "Fermat integer factorization (nested loops).",
    "fermat2": "Fermat integer factorization (single loop).",
    "freire1": "Freire's integer square root.",
    "freire1_int": "Freire's integer square root (integer-only version).",
    "freire2": "Freire's integer cube root (degree 3).",
    "geo1": "Geometric series sum.",
    "geo2": "Geometric series sum (variant).",
    "geo3": "Geometric series sum with constant factor.",
    "hard": "Hardware-style integer division.",
    "isqrt": "Integer square root.",
    "knuth": "Knuth's divisor-searching algorithm (degree 3).",
    "lcm1": "Least common multiple via GCD (three branches).",
    "lcm2": "Least common multiple via GCD (two branches).",
    "mannadiv": "Manna's integer division.",
    "prod4br": "Shift-add product with four branches.",
    "prodbin": "Product by binary shift-add.",
    "ps1": "Power sum: sum of 1s.",
    "ps2": "Power sum: sum of i (degree 2).",
    "ps3": "Power sum: sum of i^2 (degree 3).",
    "ps4": "Power sum: sum of i^3 (degree 4).",
    "ps5": "Power sum: sum of i^4 (degree 5).",
    "ps6": "Power sum: sum of i^5 (degree 6).",
    "sqrt1": "Integer square root (octagonal inequalities).",
    "wensley": "Wensley's real division approximation.",
}

SYMEX_DESCRIPTIONS = {
    "arrays": "1-D arrays as z3 arrays: reads, writes, {...} initializers.",
    "cdiv": "C division semantics: / and % truncate toward zero.",
    "defines": "#define constants and function-like macros via cpp.",
    "diverge": "Non-termination proof with a concrete diverging input (--nonterm).",
    "divider_bad": "vassert violation with a concrete counterexample input.",
    "dowhile": "do-while runs its body at least once; break exits.",
    "for_continue": "continue in a for loop still runs the increment.",
    "globals": "Global variables, zero-initialized per C rules.",
    "inline_funcs": "User-defined helper functions, inlined at call sites.",
    "isqrt": "isqrt() modeled as a fresh symbol with defining constraints.",
    "k2induction": "Invariant provable only by 2-induction (try --prove 'x != 1' with k=2).",
    "kinduction": "Unbounded loop-invariant proof (try --prove 'q*y + r == x').",
    "lexicographic": "Lexicographic termination: no single rank works (--terminates 'x ; y').",
    "merge_diamonds": "Sequential if/else diamonds merged into one state (--merge).",
    "multiphase": "Auto-synthesized 2-phase ranking function (--terminates auto).",
    "overflow_bad": "Signed 32-bit overflow found by --check-overflow.",
    "safety_bounds_bad": "Out-of-bounds array index found by the auto safety check.",
    "safety_div_bad": "Reachable division by zero found by the auto safety check.",
    "side_effects": "Side effects in conditions: while (i++ < n), pre/post ++/--.",
    "structs": "Structs by value: nested fields, typedefs, copies.",
    "switch": "switch with fallthrough, default, and break.",
    "termination": "Termination proof via ranking function (--terminates 'r' --assume 'y >= 1').",
    "ternary": "Ternary operator becomes a z3 If expression.",
    "truthiness": "C truthiness: integers as conditions mean expr != 0.",
    "unknown": "unknown()/nondet() as fresh symbolic values.",
    "unreached": "Reachability warnings for vtrace points no path hits.",
    "witness_bad": "Violation with a witness trace of branch decisions.",
}

def _symex_example_files() -> dict[str, Path]:
    """id -> path for the symex test programs (globbed, so no path traversal)."""
    if not SYMEX_DIR.is_dir():
        return {}
    return {f"symex_{p.stem}": p for p in sorted(SYMEX_DIR.glob("*.c"))}

def _example_files() -> dict[str, Path]:
    """id -> path for every servable example (globbed, so no path traversal)."""
    files = {}
    if NLA_DIR.is_dir():
        for p in sorted(NLA_DIR.glob("*.c")):
            files[f"nla_{p.stem}"] = p
    for p in sorted(EXAMPLES_DIR.glob("*.csv")):
        files[f"csv_{p.stem}"] = p
    # legacy ids used by the original frontend
    files["cohendiv"] = EXAMPLES_DIR / "cohendiv.c"
    files["bresenham"] = EXAMPLES_DIR / "bresenham.c"
    files["sqrt1"] = EXAMPLES_DIR / "sqrt1.c"
    files["cohendiv_csv"] = EXAMPLES_DIR / "cohendiv.csv"
    return files

app = Flask(__name__)
CORS(app, resources={r"/api/*": {"origins": [r"https://([a-z0-9-]+\.)?roars\.dev$", r"http://localhost:\d+$", r"http://127\.0\.0\.1:\d+$"]}})

jobs: dict[str, dict] = {}
job_lock = threading.Lock()
runner = DIGRunner()

def _cleanup_old_jobs(max_age_s: int = 3600):
    now = time.time()
    with job_lock:
        expired = [jid for jid, j in jobs.items() if now - j["created"] > max_age_s]
        for jid in expired:
            jobs.pop(jid, None)

def _worker(job_id: str):
    with job_lock:
        job = jobs.get(job_id)
        if not job or job["status"] == "cancelled":
            return
        job["status"] = "running"
        job["started"] = time.time()

    code = job["code"]
    input_type = job["input_type"]
    options = job["options"]
    tool = job.get("tool", "dig")

    def on_output(text: str):
        with job_lock:
            if jobs.get(job_id) and jobs[job_id]["status"] == "running":
                jobs[job_id]["raw_output"] += text

    def check_cancelled():
        with job_lock:
            j = jobs.get(job_id)
            return j and j["status"] == "cancelled"

    try:
        res = runner.run(code=code, input_type=input_type, options=options, on_output=on_output, check_cancelled=check_cancelled, tool=tool)
        with job_lock:
            if job["status"] == "cancelled":
                return
            job["status"] = res["status"]
            job["runtime"] = res.get("runtime")
            job["locations"] = res.get("locations", [])
            job["raw_output"] = res.get("raw_output", "")
            job["error"] = res.get("error")
            job["finished"] = time.time()
    except Exception as e:
        logger.exception(f"Error executing job {job_id}")
        with job_lock:
            job["status"] = "error"
            job["error"] = str(e)
            job["finished"] = time.time()

@app.route("/api/health", methods=["GET"])
def health():
    return jsonify({
        "status": "ok",
        "dig_root": str(DIG_ROOT),
        "active_jobs": sum(1 for j in jobs.values() if j["status"] == "running"),
        "queued_jobs": sum(1 for j in jobs.values() if j["status"] == "queued"),
    })

@app.route("/api/run", methods=["POST"])
def run_job():
    _cleanup_old_jobs()
    data = request.get_json() or {}
    code = data.get("code", "").strip()
    input_type = data.get("input_type", "c").lower()
    options = data.get("options", {})
    tool = data.get("tool", "dig").lower()

    if not code:
        return jsonify({"error": "No code or trace provided"}), 400
    if tool not in ("dig", "symex"):
        return jsonify({"error": f"Unknown tool: {tool}"}), 400

    job_id = str(uuid.uuid4())[:8]
    job = {
        "id": job_id,
        "status": "queued",
        "created": time.time(),
        "code": code,
        "input_type": input_type,
        "options": options,
        "tool": tool,
        "result": None,
        "runtime": None,
        "locations": [],
        "raw_output": "",
        "error": None,
    }

    with job_lock:
        jobs[job_id] = job

    thread = threading.Thread(target=_worker, args=(job_id,), daemon=True)
    thread.start()

    return jsonify({
        "job_id": job_id,
        "status": "queued",
        "message": f"Job queued. Use GET /api/status/{job_id} to poll progress."
    }), 202

@app.route("/api/status/<job_id>", methods=["GET"])
def status(job_id: str):
    with job_lock:
        job = jobs.get(job_id)
    if not job:
        return jsonify({"error": "Job not found"}), 404

    response = {
        "job_id": job["id"],
        "status": job["status"],
        "input_type": job["input_type"],
        "options": job["options"],
    }

    if job["status"] == "running":
        response["elapsed"] = round(time.time() - job.get("started", job["created"]), 1)
        response["raw_output"] = job["raw_output"]
    elif job["status"] in ("completed", "timeout", "error"):
        response["runtime"] = job["runtime"]
        response["locations"] = job["locations"]
        response["raw_output"] = job["raw_output"]
        response["error"] = job["error"]

    return jsonify(response)

@app.route("/api/cancel/<job_id>", methods=["POST"])
def cancel(job_id: str):
    with job_lock:
        job = jobs.get(job_id)
        if not job:
            return jsonify({"error": "Job not found"}), 404
        if job["status"] not in ("completed", "error", "cancelled", "timeout"):
            job["status"] = "cancelled"
            job["finished"] = time.time()
    return jsonify({"status": "cancelled", "message": "Job cancelled."})

@app.route("/api/examples", methods=["GET"])
def list_examples():
    examples = []
    if request.args.get("tool", "dig").lower() == "symex":
        for ex_id, path in _symex_example_files().items():
            stem = path.stem
            examples.append({
                "id": ex_id,
                "name": stem,
                "type": "c",
                "group": "SymEx test programs",
                "description": SYMEX_DESCRIPTIONS.get(stem, "Symbolic execution test program."),
                "file": path.name,
            })
        return jsonify({"examples": examples})
    for ex_id, path in _example_files().items():
        if ex_id.startswith("nla_"):
            stem = path.stem
            examples.append({
                "id": ex_id,
                "name": stem,
                "type": "c",
                "group": "NLA C benchmarks",
                "description": NLA_DESCRIPTIONS.get(stem, "NLA benchmark program."),
                "file": path.name,
            })
        elif ex_id.startswith("csv_"):
            examples.append({
                "id": ex_id,
                "name": f"{path.stem} traces",
                "type": "csv",
                "group": "CSV traces",
                "description": f"Execution trace samples for {path.stem}.",
                "file": path.name,
            })
    return jsonify({"examples": examples})

@app.route("/api/example/<example_id>", methods=["GET"])
def get_example(example_id: str):
    if example_id.startswith("symex_"):
        file_path = _symex_example_files().get(example_id)
    else:
        file_path = _example_files().get(example_id)
    if file_path and file_path.exists():
        return jsonify({
            "id": example_id,
            "content": file_path.read_text()
        })
    return jsonify({"error": "Example not found"}), 404

@app.route("/", methods=["GET"])
@app.route("/index.html", methods=["GET"])
def classic_index():
    return send_from_directory(CLASSIC_DIR, "index.html")

@app.route("/symexc.html", methods=["GET"])
def classic_symexc():
    return send_from_directory(CLASSIC_DIR, "symexc.html")

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5001))
    debug = os.environ.get("FLASK_DEBUG", "false").lower() == "true"
    print(f"DIG Web Server starting on port {port} (debug={debug})...")
    app.run(host="0.0.0.0", port=port, debug=debug)
