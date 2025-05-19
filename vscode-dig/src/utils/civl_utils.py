import argparse
import subprocess
import shlex
import json
import sys

def run_civl(file_path, symexefile, max_depth, civl_jar):
    civl_command = f"java -jar \"{civl_jar}\" verify -maxdepth={max_depth} \"{symexefile}\""

    try:
        cp = subprocess.run(
            shlex.split(civl_command),
            timeout=max_depth,
            capture_output=True,
            text=True
        )

        output = cp.stdout.strip()
        error = cp.stderr.strip()

        # Don't crash on non-zero exit, but capture all output
        result = {
            "output": output,
            "error": error if cp.returncode != 0 else None,
            "exit_code": cp.returncode
        }
        return result

    except Exception as e:
        return {
            "output": "",
            "error": f"Exception: {str(e)}",
            "exit_code": -1
        }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run CIVL on a specific assertion")
    parser.add_argument("file_path", type=str, help="Path to the source file")
    parser.add_argument("symexefile", type=str, help="Path to the instrumented C file")
    parser.add_argument("--max_depth", type=int, default=10, help="Maximum depth for CIVL verification")
    parser.add_argument("--civl_jar", type=str, required=True, help="Full path to CIVL jar file")

    args = parser.parse_args()
    result = run_civl(args.file_path, args.symexefile, args.max_depth, args.civl_jar)
    print(json.dumps(result))
