from __future__ import annotations

import os
from pathlib import Path
import shutil
import subprocess

import pytest


REPO = Path(__file__).resolve().parent.parent
CRATE = REPO / "rust" / "axiom-spike"
LOCAL_ROOT = Path("/tmp/dig-rust")


def rust_environment():
    system_cargo = shutil.which("cargo")
    system_rustc = shutil.which("rustc")
    if system_cargo and system_rustc:
        return system_cargo, {**os.environ, "RUSTC": system_rustc}
    cargo = LOCAL_ROOT / "usr" / "bin" / "cargo"
    rustc = LOCAL_ROOT / "usr" / "bin" / "rustc"
    if cargo.is_file() and rustc.is_file():
        environment = os.environ.copy()
        environment["PATH"] = f"{LOCAL_ROOT / 'usr' / 'bin'}:{environment['PATH']}"
        environment["RUSTC"] = str(rustc)
        environment["LD_LIBRARY_PATH"] = (
            f"{LOCAL_ROOT / 'usr' / 'lib' / 'x86_64-linux-gnu'}:"
            f"{LOCAL_ROOT / 'usr' / 'lib' / 'rustlib' / 'x86_64-unknown-linux-gnu' / 'lib'}"
        )
        return str(cargo), environment
    pytest.skip("Rust toolchain is unavailable")


def test_rust_ownership_and_panic_feasibility_fixtures():
    cargo, environment = rust_environment()
    completed = subprocess.run(
        [cargo, "test", "--locked", "--offline"],
        cwd=CRATE,
        env=environment,
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr

