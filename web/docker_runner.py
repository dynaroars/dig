import os
import sys
import time
import json
import tempfile
import subprocess
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

    def run(self, code: str, input_type: str = "c", options: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        options = options or {}
        timeout = min(int(options.get("timeout", 60)), 300)
        
        with tempfile.TemporaryDirectory(prefix="dig_web_") as tmpdir:
            tmppath = Path(tmpdir)
            ext = ".c" if input_type == "c" else ".csv"
            input_file = tmppath / f"prog{ext}"
            input_file.write_text(code)
            
            # Build CLI arguments for dig.py
            cmd_opts = ["-log_level", "2"]
            if options.get("maxdeg") is not None:
                cmd_opts.extend(["-maxdeg", str(options["maxdeg"])])
            if options.get("noeqts"):
                cmd_opts.append("-noeqts")
            if options.get("noieqs"):
                cmd_opts.append("-noieqs")
            if options.get("nocongruences"):
                cmd_opts.append("-nocongruences")
            if options.get("nominmaxplus"):
                cmd_opts.append("-nominmaxplus")
            if options.get("noss"):
                cmd_opts.append("-noss")
            if options.get("nomp") or self.use_docker:
                cmd_opts.append("-nomp")

            start_time = time.time()
            
            if self.use_docker:
                res = self._run_docker(input_file, cmd_opts, timeout)
            else:
                res = self._run_direct(input_file, cmd_opts, timeout)
                
            runtime = round(time.time() - start_time, 2)
            res["runtime"] = runtime
            res["locations"] = self._parse_invariants(res.get("raw_output", ""))
            return res

    def _run_docker(self, input_file: Path, cmd_opts: list, timeout: int) -> Dict[str, Any]:
        container_file = f"/dig/input/{input_file.name}"
        docker_cmd = [
            "docker", "run", "--rm",
            "--network", "none",
            "--memory", "2g",
            "--cpus", "4",
            "--pids-limit", "256",
            "-v", f"{input_file.resolve()}:{container_file}:ro",
            self.docker_image,
            "/root/miniconda3/bin/python3", "-O", "/dig/src/dig.py", container_file
        ] + cmd_opts

        try:
            proc = subprocess.run(
                docker_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout + 5
            )
            return {
                "status": "completed" if proc.returncode == 0 else "error",
                "raw_output": proc.stdout,
                "exit_code": proc.returncode
            }
        except subprocess.TimeoutExpired as e:
            return {
                "status": "timeout",
                "raw_output": e.stdout or "Execution timed out.",
                "error": f"Execution exceeded time limit of {timeout} seconds."
            }
        except Exception as e:
            return {
                "status": "error",
                "raw_output": str(e),
                "error": str(e)
            }

    def _run_direct(self, input_file: Path, cmd_opts: list, timeout: int) -> Dict[str, Any]:
        python_exe = sys.executable
        cmd = [python_exe, "-O", str(DIG_MAIN), str(input_file)] + cmd_opts
        env = os.environ.copy()
        env["PYTHONPATH"] = str(DIG_ROOT / "src") + ":" + env.get("PYTHONPATH", "")
        
        try:
            proc = subprocess.run(
                cmd,
                cwd=str(DIG_ROOT / "src"),
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=timeout,
                env=env
            )
            return {
                "status": "completed" if proc.returncode == 0 else "error",
                "raw_output": proc.stdout,
                "exit_code": proc.returncode
            }
        except subprocess.TimeoutExpired as e:
            return {
                "status": "timeout",
                "raw_output": e.stdout or "Execution timed out.",
                "error": f"Execution exceeded time limit of {timeout} seconds."
            }
        except Exception as e:
            return {
                "status": "error",
                "raw_output": str(e),
                "error": str(e)
            }

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
