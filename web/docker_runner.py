import os
import sys
import time
import json
import tempfile
import subprocess
import select
import logging
from pathlib import Path
from typing import Dict, Any, Optional

logger = logging.getLogger(__name__)

DIG_ROOT = Path(os.environ.get("DIG_ROOT", Path(__file__).resolve().parent.parent))
DIG_MAIN = DIG_ROOT / "src" / "dig.py"

class DIGRunner:
    """Manages sandboxed execution of DIG using Docker (or direct fallback)."""
    
    def __init__(self, use_docker: Optional[bool] = None):
        if use_docker is None:
            self.use_docker = os.environ.get("USE_DOCKER", "true").lower() == "true"
        else:
            self.use_docker = use_docker
            
        self.docker_image = os.environ.get("DIG_DOCKER_IMAGE", "dig-sandbox")

    def run(self, code: str, input_type: str = "c", options: Optional[Dict[str, Any]] = None, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None) -> Dict[str, Any]:
        options = options or {}
        timeout = min(int(options.get("timeout", 60)), 300)
        
        with tempfile.TemporaryDirectory(prefix="dig_web_") as tmpdir:
            tmppath = Path(tmpdir)
            ext = ".c" if input_type == "c" else ".csv"
            input_file = tmppath / f"prog{ext}"
            input_file.write_text(code)
            
            # Build CLI arguments for dig.py
            cmd_opts = ["-log_level", "3"]
            
            # Numeric options
            for opt in ["maxdeg", "maxterm", "nrandinps", "inpMaxV", "se_maxdepth", "iupper", "ideg", "iterms", "icoefs"]:
                if options.get(opt) is not None and options.get(opt) != "":
                    cmd_opts.extend([f"-{opt}", str(options[opt])])
            
            # Float options
            if options.get("seed") is not None and options.get("seed") != "":
                cmd_opts.extend(["-seed", str(options["seed"])])
                
            # Text options
            if options.get("uterms") is not None and str(options["uterms"]).strip() != "":
                cmd_opts.extend(["-uterms", str(options["uterms"])])
                
            # Boolean flags
            for opt in ["noeqts", "noieqs", "nocongruences", "nominmaxplus", "noss", "noarrays", "noincrdepth", "nosimplify", "nofilter", "nomp", "dosolverstats"]:
                if options.get(opt):
                    cmd_opts.append(f"-{opt}")

            start_time = time.time()
            
            if self.use_docker:
                res = self._run_docker(input_file, cmd_opts, timeout, on_output, check_cancelled=check_cancelled)
            else:
                res = self._run_direct(input_file, cmd_opts, timeout, on_output, check_cancelled=check_cancelled)
                
            runtime = round(time.time() - start_time, 2)
            res["runtime"] = runtime
            res["locations"] = self._parse_invariants(res.get("raw_output", ""))
            return res

    def _run_cmd_stream(self, cmd: list, timeout: int, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None, **kwargs) -> Dict[str, Any]:
        try:
            proc = subprocess.Popen(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,  # Line buffered
                **kwargs
            )
            
            start_time = time.time()
            output_lines = []
            while True:
                # Check for cancellation
                if check_cancelled and check_cancelled():
                    proc.kill()
                    proc.wait()
                    raw = "".join(output_lines)
                    return {
                        "status": "cancelled",
                        "raw_output": raw + "\nExecution cancelled by user.",
                        "error": "Execution cancelled by user."
                    }

                # Check for timeout
                elapsed = time.time() - start_time
                if elapsed > timeout:
                    proc.kill()
                    proc.wait()
                    raw = "".join(output_lines)
                    return {
                        "status": "timeout",
                        "raw_output": raw + "\nExecution timed out (exceeded limit).",
                        "error": "Execution exceeded time limit."
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
            
            try:
                returncode = proc.wait(timeout=5)
            except subprocess.TimeoutExpired:
                proc.kill()
                returncode = proc.wait()
                raw = "".join(output_lines)
                return {
                    "status": "timeout",
                    "raw_output": raw + "\nExecution timed out.",
                    "error": "Execution exceeded time limit."
                }
                
            raw = "".join(output_lines)
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

    def _run_docker(self, input_file: Path, cmd_opts: list, timeout: int, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None) -> Dict[str, Any]:
        container_file = f"/dig/input/{input_file.name}"
        docker_cmd = [
            "docker", "run", "--rm",
            "--network", "none",
            "--memory", "4g",
            "--cpuset-cpus", "0-7",
            "--pids-limit", "512",
            "-e", "PYTHONUNBUFFERED=1",
            "-v", f"{input_file.resolve()}:{container_file}:ro",
            "-v", f"{DIG_ROOT.resolve()}/src:/dig/src:ro",
            self.docker_image,
            "/root/miniconda3/bin/python3", "-u", "-O", "/dig/src/dig.py", container_file
        ] + cmd_opts

        return self._run_cmd_stream(docker_cmd, timeout + 5, on_output, check_cancelled=check_cancelled)

    def _run_direct(self, input_file: Path, cmd_opts: list, timeout: int, on_output: Optional[Any] = None, check_cancelled: Optional[Any] = None) -> Dict[str, Any]:
        python_exe = sys.executable
        cmd = [python_exe, "-u", "-O", str(DIG_MAIN), str(input_file)] + cmd_opts
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
