import os
import sys
import uuid
import json
import time
import shutil
import threading
import logging
from pathlib import Path
from flask import Flask, request, jsonify
from flask_cors import CORS

from docker_runner import DIGRunner

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

DIG_ROOT = Path(os.environ.get("DIG_ROOT", Path(__file__).resolve().parent.parent))
EXAMPLES_DIR = Path(__file__).resolve().parent / "examples"

app = Flask(__name__)
CORS(app)

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

    def on_output(text: str):
        with job_lock:
            if jobs.get(job_id) and jobs[job_id]["status"] == "running":
                jobs[job_id]["raw_output"] += text

    try:
        res = runner.run(code=code, input_type=input_type, options=options, on_output=on_output)
        with job_lock:
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

    if not code:
        return jsonify({"error": "No code or trace provided"}), 400

    job_id = str(uuid.uuid4())[:8]
    job = {
        "id": job_id,
        "status": "queued",
        "created": time.time(),
        "code": code,
        "input_type": input_type,
        "options": options,
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
    examples = [
        {
            "id": "cohendiv",
            "name": "CohenDiv (C Program)",
            "type": "c",
            "description": "Integer division with nested loops. Infers nonlinear equalities and linear inequalities.",
            "file": "cohendiv.c"
        },
        {
            "id": "bresenham",
            "name": "Bresenham (C Program)",
            "type": "c",
            "description": "Line drawing algorithm. Infers loop invariant and post-condition.",
            "file": "bresenham.c"
        },
        {
            "id": "sqrt1",
            "name": "Sqrt1 (C Program)",
            "type": "c",
            "description": "Integer square root algorithm demonstrating nonlinear octagonal inequalities.",
            "file": "sqrt1.c"
        },
        {
            "id": "cohendiv_csv",
            "name": "CohenDiv Traces (CSV)",
            "type": "csv",
            "description": "Execution trace samples for CohenDiv algorithm.",
            "file": "cohendiv.csv"
        }
    ]
    return jsonify({"examples": examples})

@app.route("/api/example/<example_id>", methods=["GET"])
def get_example(example_id: str):
    mapping = {
        "cohendiv": EXAMPLES_DIR / "cohendiv.c",
        "bresenham": EXAMPLES_DIR / "bresenham.c",
        "sqrt1": EXAMPLES_DIR / "sqrt1.c",
        "cohendiv_csv": EXAMPLES_DIR / "cohendiv.csv"
    }
    file_path = mapping.get(example_id)
    if file_path and file_path.exists():
        return jsonify({
            "id": example_id,
            "content": file_path.read_text()
        })
    return jsonify({"error": "Example not found"}), 404

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5001))
    print(f"DIG Web Server starting on port {port}...")
    app.run(host="0.0.0.0", port=port, debug=True)
