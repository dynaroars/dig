"""Isolated Python target evaluator and JSON-lines worker client."""

from __future__ import annotations

import argparse
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import dataclass
import hashlib
import importlib
import io
import json
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import tempfile
import time
from typing import Any, Mapping, TextIO

from ..model import (
    Call,
    Constant,
    PostStateProjection,
    Term,
    Variable,
    term_from_data,
    term_to_data,
)
from ..spec import Manifest, load_manifest
from .limits import resource_limiter


PROTOCOL_VERSION = 1
DEFAULT_MESSAGE_LIMIT = 1_048_576


class WorkerProtocolError(RuntimeError):
    pass


class _BoundedCapture(io.TextIOBase):
    def __init__(self, limit: int) -> None:
        self.limit = limit
        self.prefix = bytearray()
        self.digest = hashlib.sha256()
        self.count = 0

    def writable(self) -> bool:
        return True

    def write(self, text: str) -> int:
        data = text.encode("utf-8", errors="replace")
        self.digest.update(data)
        self.count += len(data)
        remaining = max(0, self.limit - len(self.prefix))
        self.prefix.extend(data[:remaining])
        return len(text)

    def result(self) -> dict[str, Any]:
        return {
            "sha256": self.digest.hexdigest(),
            "bytes": self.count,
            "truncated": self.count > len(self.prefix),
        }


def _resolve(binding: str) -> Any:
    try:
        module_name, qualified_name = binding.split(":", 1)
    except ValueError as exc:
        raise WorkerProtocolError(f"invalid Python binding {binding!r}") from exc
    value: Any = importlib.import_module(module_name)
    for component in qualified_name.split("."):
        value = getattr(value, component)
    return value


def _encoded(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, str)):
        return value
    if isinstance(value, float):
        if value != value or value in (float("inf"), float("-inf")):
            raise TypeError("non-finite float requires a custom codec")
        return value
    if isinstance(value, (list, tuple)):
        return [_encoded(child) for child in value]
    if isinstance(value, dict):
        if not all(isinstance(key, str) for key in value):
            raise TypeError("dictionary keys require strings")
        return {key: _encoded(value[key]) for key in sorted(value)}
    if isinstance(value, (set, frozenset)):
        values = [_encoded(child) for child in value]
        return {"$set": sorted(values, key=_canonical_json)}
    if isinstance(value, bytes):
        return {"$bytes_hex": value.hex()}
    raise TypeError(f"unsupported value type {type(value).__name__}")


def _canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, allow_nan=False, sort_keys=True, separators=(",", ":"))


@dataclass(slots=True)
class _Evaluated:
    value: Any
    root_ids: frozenset[str]


class _Runtime:
    def __init__(self, manifest: Manifest) -> None:
        self.manifest = manifest
        self.operations = {operation.id: operation for operation in manifest.model_operations()}
        self.operation_declarations = {
            declaration["id"]: declaration for declaration in manifest.operations
        }
        self.type_declarations = {declaration["id"]: declaration for declaration in manifest.types}
        self.callables = {
            operation_id: _resolve(declaration["binding"])
            for operation_id, declaration in self.operation_declarations.items()
        }
        self.factories = {
            type_id: _resolve(declaration["from_recipe"])
            for type_id, declaration in self.type_declarations.items()
            if declaration.get("from_recipe")
        }
        self.generators = {
            type_id: _resolve(declaration["generator"])
            for type_id, declaration in self.type_declarations.items()
            if declaration.get("generator")
        }
        self.snapshots = {
            type_id: _resolve(declaration["snapshot"])
            for type_id, declaration in self.type_declarations.items()
            if declaration.get("snapshot")
        }

    def construct(self, type_id: str, value: Any) -> Any:
        factory = self.factories.get(type_id)
        if factory is not None:
            return factory(value)
        # Round-tripping JSON creates fresh list/dict worlds without deepcopying
        # target-controlled objects.
        return json.loads(_canonical_json(value))

    def snapshot(self, type_id: str, value: Any) -> Any:
        observer = self.snapshots.get(type_id)
        return _encoded(observer(value) if observer is not None else value)

    def generate_values(self, type_id: str, seed: int, count: int) -> list[Any]:
        try:
            generator = self.generators[type_id]
        except KeyError as exc:
            raise WorkerProtocolError(f"type {type_id!r} has no recipe generator") from exc
        values = generator(seed, count)
        if not isinstance(values, (list, tuple)) or len(values) != count:
            raise WorkerProtocolError(
                f"generator for {type_id!r} must return exactly {count} recipes"
            )
        return [_encoded(value) for value in values]

    def evaluate_case(self, case: Mapping[str, Any]) -> dict[str, Any]:
        started = time.monotonic()
        output_limit = self.manifest.limits["output_limit_bytes"]
        stdout = _BoundedCapture(output_limit)
        stderr = _BoundedCapture(output_limit)
        roots: dict[str, Any] = {}
        root_types: dict[str, str] = {}
        variables: dict[tuple[str, int], _Evaluated] = {}
        mutated_roots: set[str] = set()

        recipe = case.get("recipe")
        if not isinstance(recipe, Mapping):
            raise WorkerProtocolError("case recipe must be an object")
        for root in recipe.get("roots", []):
            root_id = root["id"]
            type_id = root["type_id"]
            if root_id in roots:
                raise WorkerProtocolError(f"duplicate recipe root {root_id!r}")
            roots[root_id] = self.construct(type_id, root["value"])
            root_types[root_id] = type_id
        for variable in recipe.get("variables", []):
            root_id = variable["root_id"]
            key = (variable["type_id"], variable["index"])
            if key in variables:
                raise WorkerProtocolError(f"duplicate recipe variable {key!r}")
            if root_id not in roots:
                raise WorkerProtocolError(f"unknown recipe root {root_id!r}")
            if root_types[root_id] != variable["type_id"]:
                raise WorkerProtocolError(f"variable {key!r} has the wrong root type")
            variables[key] = _Evaluated(roots[root_id], frozenset({root_id}))

        term = term_from_data(case["term"], self.operations)

        def evaluate(node: Term) -> _Evaluated:
            if isinstance(node, Variable):
                try:
                    return variables[(node.type_id, node.index)]
                except KeyError as exc:
                    raise WorkerProtocolError(f"recipe does not bind {node!r}") from exc
            if isinstance(node, Constant):
                return _Evaluated(term_to_data(node)["value"], frozenset())
            children = tuple(evaluate(child) for child in node.children)
            operation = self.operations[node.operation_id]
            callable_ = self.callables[node.operation_id]
            arguments = [child.value for child in children]
            before = None
            if operation.pure:
                before = {
                    root_id: self.snapshot(root_types[root_id], roots[root_id])
                    for child in children
                    for root_id in child.root_ids
                }
            try:
                result = callable_(*arguments)
            except Exception as target_exception:
                if before is not None and before != {
                    root_id: self.snapshot(root_types[root_id], roots[root_id])
                    for root_id in before
                }:
                    raise WorkerProtocolError(
                        f"pure operation {operation.id!r} mutated an input before throwing"
                    ) from target_exception
                raise
            if before is not None and before != {
                root_id: self.snapshot(root_types[root_id], roots[root_id])
                for root_id in before
            }:
                raise WorkerProtocolError(f"pure operation {operation.id!r} mutated an input")
            for index in operation.mutates:
                mutated_roots.update(children[index].root_ids)
            if isinstance(node.projection, PostStateProjection):
                return children[node.projection.input_index]
            result_roots = frozenset(
                root_id for root_id, root_value in roots.items() if result is root_value
            )
            return _Evaluated(result, result_roots)

        try:
            with redirect_stdout(stdout), redirect_stderr(stderr):
                result = evaluate(term)
            status = "returned"
            return_value = self.snapshot(term.type_id, result.value)
            exception = None
        except WorkerProtocolError as exc:
            status = "protocol_error"
            return_value = None
            exception = None
            protocol_detail = str(exc)
        except Exception as exc:  # target exception is data, not a worker failure
            status = "threw"
            return_value = None
            exception = {
                "class": f"{type(exc).__module__}.{type(exc).__qualname__}",
                "payload": str(exc)[:1024],
            }

        requested = case.get("observe_roots", [])
        observed_ids = sorted(mutated_roots | set(requested))
        observations = {
            root_id: {
                "observer_id": self.type_declarations[root_types[root_id]].get(
                    "snapshot", "builtin-json-v1"
                ),
                "value": self.snapshot(root_types[root_id], roots[root_id]),
            }
            for root_id in observed_ids
        }
        outcome = {
            "status": status,
            "return_value": return_value,
            "observations_by_root": observations,
            "aliases": [],
            "exception": exception,
            "stdout": stdout.result(),
            "stderr": stderr.result(),
            "elapsed_ms": max(0, round((time.monotonic() - started) * 1000)),
        }
        if status == "protocol_error":
            outcome["detail"] = protocol_detail
        return outcome


def _write_message(stream: TextIO, message: Mapping[str, Any]) -> None:
    stream.write(_canonical_json(message) + "\n")
    stream.flush()


def _worker_main(manifest_path: Path) -> int:
    manifest = load_manifest(manifest_path)
    for module_root in manifest.target.get("module_roots", []):
        resolved = (manifest.source.parent / module_root).resolve()
        sys.path.insert(0, str(resolved))
    runtime = _Runtime(manifest)
    for line in sys.stdin:
        if len(line.encode("utf-8")) > DEFAULT_MESSAGE_LIMIT:
            raise WorkerProtocolError("protocol message exceeds the size limit")
        request = json.loads(line)
        if request.get("protocol_version") != PROTOCOL_VERSION:
            raise WorkerProtocolError("unsupported protocol version")
        message = request.get("message")
        if message == "hello":
            response = {
                "protocol_version": PROTOCOL_VERSION,
                "message": "hello",
                "language": "python",
                "capabilities": ["evaluate_terms"],
            }
        elif message == "evaluate_batch":
            cases = request.get("cases")
            if not isinstance(cases, list):
                raise WorkerProtocolError("batch cases must be an array")
            response = {
                "protocol_version": PROTOCOL_VERSION,
                "message": "batch_result",
                "batch_id": request.get("batch_id"),
                "results": [
                    {"case_id": case.get("case_id"), "outcome": runtime.evaluate_case(case)}
                    for case in cases
                ],
            }
        elif message == "generate_values":
            type_id = request.get("type_id")
            seed = request.get("seed")
            count = request.get("count")
            if not isinstance(type_id, str) or type(seed) is not int or type(count) is not int:
                raise WorkerProtocolError("generate_values requires type_id, integer seed, and count")
            if count < 1 or count > 100_000:
                raise WorkerProtocolError("generate_values count is outside the allowed range")
            response = {
                "protocol_version": PROTOCOL_VERSION,
                "message": "generated_values",
                "type_id": type_id,
                "values": runtime.generate_values(type_id, seed, count),
            }
        elif message == "shutdown":
            _write_message(
                sys.stdout,
                {"protocol_version": PROTOCOL_VERSION, "message": "shutdown"},
            )
            return 0
        else:
            raise WorkerProtocolError(f"unknown message {message!r}")
        _write_message(sys.stdout, response)
    return 0


class PythonWorker:
    """Parent-side owner of one isolated, restartable Python worker process."""

    def __init__(
        self,
        manifest_path: Path | str,
        *,
        python_executable: Path | str = sys.executable,
        timeout: float = 30.0,
        message_limit: int = DEFAULT_MESSAGE_LIMIT,
        max_batches: int = 100,
    ) -> None:
        self.manifest_path = Path(manifest_path).resolve()
        self.python_executable = str(python_executable)
        self.timeout = timeout
        self.message_limit = message_limit
        self.max_batches = max_batches
        self.batches_completed = 0
        self.process: subprocess.Popen[str] | None = None
        self._run_directory: tempfile.TemporaryDirectory[str] | None = None

    def __enter__(self) -> PythonWorker:
        self.start()
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def start(self) -> None:
        if self.process is not None:
            return
        if self.max_batches < 1:
            raise ValueError("max_batches must be positive")
        manifest = load_manifest(self.manifest_path)
        self._run_directory = tempfile.TemporaryDirectory(prefix="dig-axiom-python-")
        self.process = subprocess.Popen(
            [
                self.python_executable,
                "-m",
                "axioms.workers.python_worker",
                "--serve",
                str(self.manifest_path),
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
            cwd=self._run_directory.name,
            preexec_fn=resource_limiter(
                memory_mib=manifest.limits["worker_memory_mib"],
                cpu_seconds=self.timeout,
            ),
            env={**os.environ, "PYTHONPATH": str(Path(__file__).resolve().parents[2])},
        )
        response = self.request({"message": "hello", "run_id": "local"})
        if response.get("message") != "hello":
            self.close()
            raise WorkerProtocolError("worker did not complete the handshake")
        self.batches_completed = 0

    def request(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        process = self.process
        if process is None or process.stdin is None or process.stdout is None:
            raise WorkerProtocolError("worker is not running")
        message = {"protocol_version": PROTOCOL_VERSION, **payload}
        encoded = _canonical_json(message)
        if len(encoded.encode("utf-8")) > self.message_limit:
            raise WorkerProtocolError("outgoing message exceeds the size limit")
        try:
            process.stdin.write(encoded + "\n")
            process.stdin.flush()
        except BrokenPipeError as exc:
            raise WorkerProtocolError(self._failure_detail("worker exited")) from exc

        selector = selectors.DefaultSelector()
        selector.register(process.stdout, selectors.EVENT_READ)
        ready = selector.select(self.timeout)
        selector.close()
        if not ready:
            self._terminate()
            raise TimeoutError(f"worker did not respond within {self.timeout:g}s")
        line = process.stdout.readline()
        if not line:
            raise WorkerProtocolError(self._failure_detail("worker closed its output"))
        if len(line.encode("utf-8")) > self.message_limit:
            self._terminate()
            raise WorkerProtocolError("incoming message exceeds the size limit")
        response = json.loads(line)
        if response.get("protocol_version") != PROTOCOL_VERSION:
            raise WorkerProtocolError("worker returned an unsupported protocol version")
        return response

    def evaluate_batch(self, batch_id: str, cases: list[Mapping[str, Any]]) -> list[dict[str, Any]]:
        if self.batches_completed >= self.max_batches:
            self.close()
            self.start()
        response = self.request(
            {"message": "evaluate_batch", "batch_id": batch_id, "cases": cases}
        )
        if response.get("message") != "batch_result" or response.get("batch_id") != batch_id:
            raise WorkerProtocolError("worker returned a mismatched batch")
        results = response.get("results")
        if not isinstance(results, list) or len(results) != len(cases):
            raise WorkerProtocolError("worker returned an incomplete batch")
        self.batches_completed += 1
        return results

    def generate_values(self, type_id: str, *, seed: int, count: int) -> list[Any]:
        response = self.request(
            {"message": "generate_values", "type_id": type_id, "seed": seed, "count": count}
        )
        if response.get("message") != "generated_values" or response.get("type_id") != type_id:
            raise WorkerProtocolError("worker returned mismatched generated values")
        values = response.get("values")
        if not isinstance(values, list) or len(values) != count:
            raise WorkerProtocolError("worker returned the wrong number of generated values")
        return values

    def close(self) -> None:
        process = self.process
        self.process = None
        if process is not None and process.poll() is None:
            try:
                self.process = process
                self.request({"message": "shutdown"})
                self.process = None
                process.wait(timeout=1)
            except (OSError, TimeoutError, WorkerProtocolError, subprocess.TimeoutExpired):
                self.process = None
                self._terminate_process(process)
        if process is not None:
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
        if self._run_directory is not None:
            self._run_directory.cleanup()
            self._run_directory = None

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
            for stream in (process.stdin, process.stdout, process.stderr):
                if stream is not None:
                    stream.close()
            if self._run_directory is not None:
                self._run_directory.cleanup()
                self._run_directory = None

    @staticmethod
    def _terminate_process(process: subprocess.Popen[str]) -> None:
        if process.poll() is not None:
            return
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            process.kill()
        process.wait(timeout=2)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--serve", type=Path, required=True, metavar="MANIFEST")
    arguments = parser.parse_args()
    return _worker_main(arguments.serve)


if __name__ == "__main__":
    raise SystemExit(main())
