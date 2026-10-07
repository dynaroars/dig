"""Parent-side lifecycle for the long-lived JVM axiom worker."""

from __future__ import annotations

import json
import os
from pathlib import Path
import selectors
import shutil
import signal
import subprocess
import sys
import tempfile
from typing import Any, Mapping

from ..spec import Manifest, load_manifest
from .python_worker import DEFAULT_MESSAGE_LIMIT, PROTOCOL_VERSION, WorkerProtocolError


_RUNNER_CLASS = "org.dynaroars.dig.axioms.Runner"
_RUNNER_SOURCE = (
    Path(__file__).resolve().parents[3]
    / "jvm"
    / "axiom-runner"
    / "src"
    / "main"
    / "java"
    / "org"
    / "dynaroars"
    / "dig"
    / "axioms"
    / "Runner.java"
)


class JavaWorker:
    def __init__(
        self,
        manifest_path: Path | str,
        *,
        java_executable: Path | str = "java",
        javac_executable: Path | str = "javac",
        timeout: float = 30.0,
        message_limit: int = DEFAULT_MESSAGE_LIMIT,
        compiler_environment: Mapping[str, str] | None = None,
    ) -> None:
        self.manifest: Manifest = load_manifest(manifest_path)
        if self.manifest.language != "java":
            raise ValueError("JavaWorker requires a Java manifest")
        self.java_executable = str(java_executable)
        self.javac_executable = str(javac_executable)
        self.timeout = timeout
        self.message_limit = message_limit
        self.compiler_environment = dict(compiler_environment or {})
        self.process: subprocess.Popen[str] | None = None
        self._build_directory: tempfile.TemporaryDirectory[str] | None = None

    def __enter__(self) -> JavaWorker:
        self.start()
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def start(self) -> None:
        if self.process is not None:
            return
        self._build_directory = tempfile.TemporaryDirectory(prefix="dig-axiom-jvm-")
        classes = Path(self._build_directory.name) / "classes"
        classes.mkdir()
        environment = {**os.environ, **self.compiler_environment}
        compilation = subprocess.run(
            [self.javac_executable, "-d", str(classes), str(_RUNNER_SOURCE)],
            capture_output=True,
            text=True,
            timeout=self.timeout,
            env=environment,
        )
        if compilation.returncode:
            self._build_directory.cleanup()
            self._build_directory = None
            raise WorkerProtocolError(
                "failed to compile the JVM worker: " + (compilation.stderr or compilation.stdout)
            )
        classpath = [str(classes)]
        classpath.extend(
            str((self.manifest.source.parent / path).resolve())
            for path in self.manifest.target.get("classpath", ())
        )
        jar = self.manifest.target.get("jar")
        if jar:
            classpath.append(str((self.manifest.source.parent / jar).resolve()))
        self.process = subprocess.Popen(
            [
                self.java_executable,
                f"-Xmx{self.manifest.limits['worker_memory_mib']}m",
                "-Xss1m",
                "-cp",
                os.pathsep.join(classpath),
                _RUNNER_CLASS,
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
            cwd=self._build_directory.name,
        )
        response = self.request(
            {
                "message": "hello",
                "run_id": "local",
                "config": {
                    "types": list(self.manifest.types),
                    "operations": list(self.manifest.operations),
                    "output_limit_bytes": self.manifest.limits["output_limit_bytes"],
                },
            }
        )
        if response.get("message") != "hello":
            self.close()
            raise WorkerProtocolError("JVM worker did not complete the handshake")

    def request(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        process = self.process
        if process is None or process.stdin is None or process.stdout is None:
            raise WorkerProtocolError("JVM worker is not running")
        message = {"protocol_version": PROTOCOL_VERSION, **payload}
        encoded = json.dumps(
            message, ensure_ascii=False, allow_nan=False, sort_keys=True, separators=(",", ":")
        )
        if len(encoded.encode()) > self.message_limit:
            raise WorkerProtocolError("outgoing JVM message exceeds the size limit")
        try:
            process.stdin.write(encoded + "\n")
            process.stdin.flush()
        except BrokenPipeError as exc:
            raise WorkerProtocolError(self._failure_detail("JVM worker exited")) from exc
        selector = selectors.DefaultSelector()
        selector.register(process.stdout, selectors.EVENT_READ)
        ready = selector.select(self.timeout)
        selector.close()
        if not ready:
            self._terminate()
            raise TimeoutError(f"JVM worker did not respond within {self.timeout:g}s")
        line = process.stdout.readline()
        if not line:
            raise WorkerProtocolError(self._failure_detail("JVM worker closed its output"))
        if len(line.encode()) > self.message_limit:
            self._terminate()
            raise WorkerProtocolError("incoming JVM message exceeds the size limit")
        response = json.loads(line)
        if response.get("protocol_version") != PROTOCOL_VERSION:
            raise WorkerProtocolError("JVM worker returned an unsupported protocol version")
        return response

    def evaluate_batch(self, batch_id: str, cases: list[Mapping[str, Any]]) -> list[dict[str, Any]]:
        response = self.request(
            {"message": "evaluate_batch", "batch_id": batch_id, "cases": cases}
        )
        if response.get("message") != "batch_result" or response.get("batch_id") != batch_id:
            raise WorkerProtocolError("JVM worker returned a mismatched batch")
        results = response.get("results")
        if not isinstance(results, list) or len(results) != len(cases):
            raise WorkerProtocolError("JVM worker returned an incomplete batch")
        return results

    def close(self) -> None:
        process = self.process
        self.process = None
        if process is not None:
            if process.poll() is None:
                try:
                    self.process = process
                    self.request({"message": "shutdown"})
                    self.process = None
                    process.wait(timeout=1)
                except (OSError, TimeoutError, WorkerProtocolError, subprocess.TimeoutExpired):
                    self.process = None
                    self._terminate_process(process)
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
        if self._build_directory is not None:
            self._build_directory.cleanup()
            self._build_directory = None

    def _failure_detail(self, prefix: str) -> str:
        process = self.process
        detail = ""
        if process is not None and process.poll() is not None and process.stderr is not None:
            detail = process.stderr.read(4096).strip()
        return f"{prefix}: {detail}" if detail else prefix

    def _terminate(self) -> None:
        if self.process is not None:
            process = self.process
            self.process = None
            self._terminate_process(process)

    @staticmethod
    def _terminate_process(process: subprocess.Popen[str]) -> None:
        if process.poll() is not None:
            return
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            process.kill()
        process.wait(timeout=2)


def find_java_tools() -> tuple[str, str] | None:
    """Return system Java tools when a full JDK is installed."""

    java = shutil.which("java")
    javac = shutil.which("javac")
    return (java, javac) if java and javac else None
