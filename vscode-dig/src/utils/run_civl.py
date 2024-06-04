import sys
import subprocess
import shlex
import json
import os

def run_civl(symexefile, max_depth):
    civl_command = f"civl verify -maxdepth={max_depth} {symexefile}"
    try:
        cp = subprocess.run(
            shlex.split(civl_command),
            timeout=max_depth,
            capture_output=True,
            check=True,
            text=True
        )
        output_lines = cp.stdout.splitlines()
        relevant_output = "\n".join(line for line in output_lines if "CIVL" not in line)
        violation = "Violation" in cp.stdout
        return {"file": symexefile, "output": relevant_output, "error": None, "violation": violation}
    except subprocess.CalledProcessError as e:
        return {"file": symexefile, "output": e.stdout.strip(), "error": e.stderr.strip(), "violation": True}

def main(symexefile, max_depth):
    result = run_civl(symexefile, max_depth)
    results_file = os.path.join(os.path.dirname(symexefile), 'civl_results.json')
    with open(results_file, 'w') as f:
        json.dump(result, f)
    print(f"Results saved to {results_file}")

if __name__ == "__main__":
    symexefile = sys.argv[1]
    max_depth = int(sys.argv[2])
    main(symexefile, max_depth)
