import os
import sys
import time
import json
import signal
import tempfile
import subprocess
import select
import logging
from pathlib import Path
from typing import Dict, Any, Optional

logger = logging.getLogger(__name__)

DIG_ROOT = Path(os.environ.get("DIG_ROOT", Path(__file__).resolve().parent.parent))

# dig.py options exposed to the web API, mirroring src/dig.py's argparse.
# File-path and benchmark options (-writeresults, -readsstates, -tmpdir,
# -benchmark_times, ...) are deliberately excluded.
INT_OPTS = [
    "maxdeg", "maxterm", "nrandinps", "inpMaxV", "se_maxdepth",
    "iupper", "ideg", "iterms", "icoefs", "llm_rounds",
]
BOOL_OPTS = [
    "noss", "nomp", "dosolverstats", "llm", "llm_no_traces",
    # advanced algorithm toggles (see ANALYSIS.md)
    "dosymba", "norecurrencemp", "nollmhoudini",
]
# string options passed through verbatim as "-<name> <value>"
STR_OPTS = ["types"]  # invariant-type allowlist (replaces the -no<type> flags)

# symex_c.py CLI options exposed to the web API (tool == "symex").
# --gen-harness is excluded (writes a file the web runner never returns).
SYMEX_INT_OPTS = ["depth", "loop", "k", "phases"]
SYMEX_BOOL_OPTS = ["gen_tests", "no_safety", "check_overflow", "merge",
                   "nonterm"]
SYMEX_LIST_OPTS = ["prove", "houdini", "assume"]  # ";"-separated exprs
# note: "terminates" is NOT a list opt — its value may itself contain ";"
# (a lexicographic tuple "x ; y") or be the keyword "auto", and is passed
# through verbatim as one argument below

class DIGRunner:
    """Manages sandboxed execution of DIG using Docker (or direct fallback)."""
    
    def __init__(self, use_docker: Optional[bool] = None):
        if use_docker is None:
            self.use_docker = os.environ.get("USE_DOCKER", "true").lower() == "true"
        else:
            self.use_docker = use_docker
            
        self.docker_image = os.environ.get("DIG_DOCKER_IMAGE", "dig-sandbox")
        # Docker bind mounts are resolved by the host daemon. A web service may
        # have a private /tmp namespace, so production can provide an explicit
        # host-visible state directory without changing tempfile globally.
        job_dir = os.environ.get("DIG_JOB_DIR")
        self.job_dir = Path(job_dir).resolve() if job_dir else None

    def run(self, code: str, input_type: str = "c", options: Optional[Dict[str, Any]] = None, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None, tool: str = "dig") -> Dict[str, Any]:
        options = options or {}
        timeout = min(int(options.get("timeout", 60)), 300)

        with tempfile.TemporaryDirectory(prefix="dig_web_", dir=self.job_dir) as tmpdir:
            tmppath = Path(tmpdir)
            ext = ".c" if input_type == "c" else ".csv"
            input_file = tmppath / f"prog{ext}"
            input_file.write_text(code)

            if tool == "symex":
                cmd_opts = self._build_symex_cmd_opts(options)
                script = "data/symex_c.py"
            else:
                cmd_opts = self._build_cmd_opts(options)
                script = "dig.py"

            start_time = time.time()

            if self.use_docker:
                res = self._run_docker(input_file, cmd_opts, timeout, on_output, check_cancelled=check_cancelled, script=script)
            else:
                res = self._run_direct(input_file, cmd_opts, timeout, on_output, check_cancelled=check_cancelled, script=script)

            runtime = round(time.time() - start_time, 2)
            res["runtime"] = runtime
            if tool == "symex":
                # symex_c exits 1 when a vassert/safety check or proof query
                # fails; that is a result to display, not an execution error
                if res.get("status") == "error" and res.get("exit_code") == 1:
                    res["status"] = "completed"
                res["locations"] = []
            else:
                res["locations"] = self._parse_invariants(res.get("raw_output", ""))
            return res

    def _build_cmd_opts(self, options: Dict[str, Any]) -> list:
        """Translate the web options dict into dig.py CLI arguments."""
        cmd_opts = ["-log_level", str(int(options.get("log_level", 3)))]
        if options.get("seed") not in (None, ""):
            cmd_opts.extend(["-seed", str(float(options["seed"]))])
        for name in INT_OPTS:
            val = options.get(name)
            if val not in (None, ""):
                cmd_opts.extend([f"-{name}", str(int(val))])
        for name in BOOL_OPTS:
            if options.get(name):
                cmd_opts.append(f"-{name}")
        for name in STR_OPTS:
            if options.get(name):
                cmd_opts.extend([f"-{name}", str(options[name])])
        if options.get("uterms"):
            cmd_opts.extend(["-uterms", str(options["uterms"])])
        return cmd_opts

    def _build_symex_cmd_opts(self, options: Dict[str, Any]) -> list:
        """Translate the web options dict into symex_c.py CLI arguments."""
        cmd_opts = []
        for name in SYMEX_INT_OPTS:
            val = options.get(name)
            if val not in (None, ""):
                cmd_opts.extend([f"--{name}", str(int(val))])
        for name in SYMEX_BOOL_OPTS:
            if options.get(name):
                cmd_opts.append("--" + name.replace("_", "-"))
        for name in SYMEX_LIST_OPTS:
            for expr in str(options.get(name) or "").split(";"):
                if expr.strip():
                    cmd_opts.extend([f"--{name}", expr.strip()])
        if str(options.get("terminates") or "").strip():
            cmd_opts.extend(["--terminates", str(options["terminates"]).strip()])
        # check_inv: "LOC EXPR" pairs separated by ";", e.g. "vtrace1 q*y + r == x"
        for item in str(options.get("check_inv") or "").split(";"):
            parts = item.strip().split(None, 1)
            if len(parts) == 2:
                cmd_opts.extend(["--check-inv", parts[0], parts[1]])
        return cmd_opts

    def _run_cmd_stream(self, cmd: list, timeout: int, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None, **kwargs) -> Dict[str, Any]:
        try:
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,  # Line buffered
                start_new_session=True,  # own process group, so timeout kill reaps mp children too
                **kwargs
            )

            def _kill_group():
                # SIGKILL the whole process group so DIG's fork-pool workers
                # die with the parent; killing just proc would orphan them
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except (ProcessLookupError, PermissionError):
                    proc.kill()
                proc.wait()

            start_time = time.time()
            output_lines = []
            while True:
                # Check for cancellation
                if check_cancelled and check_cancelled():
                    _kill_group()
                    raw = "".join(output_lines)
                    return {
                        "status": "cancelled",
                        "raw_output": raw + "\nExecution cancelled by user.",
                        "error": "Execution cancelled by user."
                    }

                # Check for timeout
                elapsed = time.time() - start_time
                if elapsed > timeout:
                    _kill_group()
                    raw = "".join(output_lines)
                    return {
                        "status": "timeout",
                        "raw_output": raw + "\nExecution timed out.",
                        "error": f"Execution exceeded time limit ({timeout}s)."
                    }

                # Check if process stdout is ready to read
                rlist, _, _ = select.select([proc.stdout], [], [], 1.0)
                if proc.stdout in rlist:
                    line = proc.stdout.readline()
                    if not line: # EOF
                        if proc.poll() is not None:
                            break
                    else:
                        output_lines.append(line)
                        if on_output:
                            try:
                                on_output(line)
                            except Exception:
                                pass
                else:
                    # Timeout of 1.0s on select, check if process died
                    if proc.poll() is not None:
                        # Process died, flush any remaining output
                        for line in proc.stdout:
                            output_lines.append(line)
                            if on_output:
                                try:
                                    on_output(line)
                                except Exception:
                                    pass
                        break

            raw = "".join(output_lines)


            try:
                returncode = proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                returncode = proc.wait()

            return {
                "status": "completed" if returncode == 0 else "error",
                "raw_output": raw,
                "exit_code": returncode
            }
        except Exception as e:
            return {
                "status": "error",
                "raw_output": str(e),
                "error": str(e)
            }

    def _run_docker(self, input_file: Path, cmd_opts: list, timeout: int, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None, script: str = "dig.py") -> Dict[str, Any]:
        container_file = f"/dig/input/{input_file.name}"
        docker_cmd = [
            "docker", "run", "--rm",
            "--network", "none",
            "--memory", "8g",
            "--cpuset-cpus", "0-7",
            "--pids-limit", "512",
            "-e", "PYTHONUNBUFFERED=1",
            "-v", f"{input_file.resolve()}:{container_file}:ro",
            "-v", f"{DIG_ROOT.resolve()}/src:/dig/src:ro",
            self.docker_image,
            # coreutils timeout inside the container: killing the local docker
            # client would leave the container running
            "timeout", "--signal=KILL", str(timeout),
            "/root/miniconda3/bin/python3", "-u", "-O", f"/dig/src/{script}", container_file
        ] + cmd_opts

        return self._run_cmd_stream(docker_cmd, timeout + 5, on_output, check_cancelled=check_cancelled)

    def _run_direct(self, input_file: Path, cmd_opts: list, timeout: int, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None, script: str = "dig.py") -> Dict[str, Any]:
        python_exe = sys.executable
        cmd = [python_exe, "-u", "-O", str(DIG_ROOT / "src" / script), str(input_file)] + cmd_opts
        env = os.environ.copy()
        env["PYTHONPATH"] = str(DIG_ROOT / "src") + ":" + env.get("PYTHONPATH", "")
        env["PYTHONUNBUFFERED"] = "1"
        
        return self._run_cmd_stream(
            cmd,
            timeout,
            on_output,
            check_cancelled=check_cancelled,
            cwd=str(DIG_ROOT / "src"),
            env=env
        )

    def _parse_invariants(self, output: str) -> list:
        """Parses output log to extract invariants grouped by vtrace location."""
        locations = []
        current_loc = None
        
        lines = output.splitlines()
        for line in lines:
            line_s = line.strip()
            # Match location header like "vtrace1(17 invs):" or "vtrace1 (17 invs):"
            if "invs):" in line_s:
                parts = line_s.split("(")
                loc_name = parts[0].strip()
                current_loc = {
                    "name": loc_name,
                    "header": line_s,
                    "invariants": []
                }
                locations.append(current_loc)
            elif current_loc and line_s:
                # Handle Category list format: "  Eqt: a*y - b == 0; q*y + r - x == 0"
                if ":" in line_s and not any(op in line_s.split(":", 1)[0] for op in ["<", ">", "=", "!"]):
                    cat_part, invs_part = line_s.split(":", 1)
                    cat_name = cat_part.strip()
                    type_map = {
                        "Eqt": "equality",
                        "Oct": "inequality",
                        "MinMax": "minmax",
                        "Congruence": "congruence",
                        "Array": "array",
                        "LLM": "llm"
                    }
                    inv_type = type_map.get(cat_name, "equality")
                    
                    invs = [inv.strip() for inv in invs_part.split(";") if inv.strip()]
                    for inv_text in invs:
                        current_loc["invariants"].append({
                            "text": inv_text,
                            "type": inv_type
                        })
                # Handle Numbered list format: "1. a*y - b == 0"
                elif line_s[0].isdigit() and "." in line_s[:4]:
                    inv_text = line_s.split(".", 1)[1].strip()
                    inv_type = "equality"
                    if "===" in inv_text or "mod" in inv_text:
                        inv_type = "congruence"
                    elif "<=" in inv_text or ">=" in inv_text or "<" in inv_text or ">" in inv_text:
                        if "max(" in inv_text or "min(" in inv_text:
                            inv_type = "minmax"
                        else:
                            inv_type = "inequality"
                    current_loc["invariants"].append({
                        "text": inv_text,
                        "type": inv_type
                    })
                
        return locations
