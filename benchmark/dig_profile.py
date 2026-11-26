"""Run DIG with periodic Python stack dumps in its internal workers."""
import faulthandler
import os
import runpy
import sys
import threading
import time
from pathlib import Path


def arm():
    faulthandler.dump_traceback_later(30, repeat=True)


faulthandler.enable()
entry = Path(__file__).resolve().parent.parent / "src/dig.py"
sys.path.insert(0, str(entry.parent))
import helpers.miscs as mp

original_worker = mp._mp_run_worker


def traced_worker(*args):
    stopped = threading.Event()
    started, cpu_started = time.monotonic(), time.process_time()

    def monitor():
        while not stopped.wait(30):
            wait_file = Path(f"/proc/self/task/{os.getpid()}/wchan")
            wait = wait_file.read_text().strip() if wait_file.exists() else "unknown"
            print(f"PROFILE worker={args[0]} elapsed={time.monotonic()-started:.2f} "
                  f"cpu={time.process_time()-cpu_started:.2f} wait={wait}", flush=True)

    watcher = threading.Thread(target=monitor, daemon=True)
    watcher.start()
    arm()
    try:
        return original_worker(*args)
    finally:
        faulthandler.cancel_dump_traceback_later()
        stopped.set()
        watcher.join()


mp._mp_run_worker = traced_worker
# Cancel the watchdog before forking; inheriting an active watchdog can
# deadlock the profiler itself when a child tries to start its own timer.
os.register_at_fork(before=faulthandler.cancel_dump_traceback_later,
                    after_in_parent=arm)
arm()
sys.argv = [str(entry), *sys.argv[1:]]
runpy.run_path(str(entry), run_name="__main__")
