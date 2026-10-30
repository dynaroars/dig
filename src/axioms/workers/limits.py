"""Best-effort POSIX resource limits for untrusted target workers."""

from __future__ import annotations

import math
import resource
from typing import Callable


def resource_limiter(*, memory_mib: int, cpu_seconds: float) -> Callable[[], None]:
    memory_bytes = memory_mib * 1024 * 1024
    cpu_limit = max(1, math.ceil(cpu_seconds))

    def apply() -> None:
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_limit, cpu_limit + 1))
        resource.setrlimit(resource.RLIMIT_AS, (memory_bytes, memory_bytes))
        resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024 * 1024, 16 * 1024 * 1024))
        if hasattr(resource, "RLIMIT_NPROC"):
            resource.setrlimit(resource.RLIMIT_NPROC, (16, 16))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    return apply

