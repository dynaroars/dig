import argparse
import subprocess
import shlex
import json

def run_civl(file_path, symexefile, max_depth):
    civl_command = f"civl verify -maxdepth={max_depth} {symexefile}"
    # print(f"Running: {civl_command}")

    try:
        cp = subprocess.run(
            shlex.split(civl_command),
            timeout=max_depth,
            capture_output=True,
            check=True,
            text=True
        )
     # Capture only the relevant output part
        output_lines = cp.stdout.splitlines()
        relevant_output = "\n".join(line for line in output_lines if "CIVL" not in line)
        return {"output": relevant_output, "error": None}
    except subprocess.CalledProcessError as e:
        return {"output": str(e.output), "error": str(e)}

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run CIVL on a specific assertion")
    parser.add_argument("file_path", type=str, help="Path to the source file")
    parser.add_argument("symexefile", type=str, help="Path to the instrumented C file")
    parser.add_argument("--max_depth", type=int, default=10, help="Maximum depth for CIVL verification")

    args = parser.parse_args()

    output = run_civl(args.file_path, args.symexefile, args.max_depth)
    print(json.dumps(output))
