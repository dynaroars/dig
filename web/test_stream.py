import sys
import time
from pathlib import Path
from docker_runner import DIGRunner

def main():
    runner = DIGRunner()
    # Read a sample program code
    example_path = Path(__file__).resolve().parent / "examples" / "cohendiv.c"
    if not example_path.exists():
        print(f"Example program not found at {example_path}")
        return

    code = example_path.read_text()
    
    print("Starting DIG solver test stream...")
    start = time.time()
    
    def on_output(text):
        elapsed = time.time() - start
        print(f"[{elapsed:.1f}s] STREAM: {text.strip()}")
        sys.stdout.flush()

    res = runner.run(code=code, input_type="c", on_output=on_output)
    print("Execution finished.")
    print("Status:", res.get("status"))

if __name__ == "__main__":
    main()
