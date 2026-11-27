"""Run Lean 4 on a DIG certificate and decide whether it certifies.

A certificate *body* (a Lean namespace defining `State`, `prog`, and
`theorem mainQ_certified : Safe prog`) is concatenated after the trusted
kernel `lean/DigCert.lean`. The runner appends two checks that Lean itself
evaluates:

  * `example : _root_.DigCert.Safe NS.prog := NS.mainQ_certified`
    pins the theorem statement to the fixed template (a body cannot shadow
    `Safe` or weaken the precondition and still pass), and
  * `#print axioms NS.mainQ_certified`, which must list only the standard
    axioms. Failed VCs are admitted by `dig_discharge` (so all failures are
    reported in one run), which shows up here as `sorryAx`.

A certificate is accepted only if Lean exits 0, reports no errors and no
`DIG_VC_FAILED`, the statement check passes, and the axioms are standard.
"""

import hashlib
import re
import shutil
import subprocess
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0"
KERNEL_PATH = Path(__file__).resolve().parent / "lean" / "DigCert.lean"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
# Cheap textual pre-check on the (untrusted) body; the axiom check is the
# authoritative one.
BANNED_TOKENS = ("sorry", "admit", "axiom", "native_decide", "implemented_by",
                 "extern", "unsafe", "set_option", "import")
THEOREM = "mainQ_certified"

_AXIOMS_RE = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
_NO_AXIOMS_RE = re.compile(r"'([^']+)' does not depend on any axioms")
_FAILED_RE = re.compile(r"DIG_VC_FAILED (\S+)")
_ERROR_RE = re.compile(r":\d+:\d+: error")
_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


class LeanUnavailable(RuntimeError):
    pass


@dataclass
class LeanResult:
    certified: bool
    status: str                      # certified | failed | rejected | error | timeout
    namespace: str
    failed_tags: list[str] = field(default_factory=list)
    axioms: list[str] | None = None
    reason: str | None = None
    returncode: int | None = None
    elapsed_sec: float = 0.0
    lean_version: str | None = None
    certificate_path: str | None = None
    certificate_sha256: str | None = None
    output: str = ""

    def to_dict(self) -> dict:
        d = asdict(self)
        d.pop("output")
        return d


def _works(cmd: list[str]) -> str | None:
    try:
        p = subprocess.run([*cmd, "--version"], capture_output=True,
                           text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return None
    if p.returncode != 0 or "no default toolchain" in (p.stderr + p.stdout):
        return None
    return p.stdout.strip()


def resolve_lean(lean_bin: str | None = None) -> tuple[list[str], str]:
    """Lean command and its version: explicit binary, then `lean` on PATH,
    then the pinned toolchain via `elan run`."""
    candidates: list[list[str]] = []
    if lean_bin:
        candidates.append([lean_bin])
    if shutil.which("lean"):
        candidates.append(["lean"])
    if shutil.which("elan"):
        candidates.append(["elan", "run", LEAN_TOOLCHAIN, "lean"])
    for cmd in candidates:
        ver = _works(cmd)
        if ver is not None:
            return cmd, ver
    raise LeanUnavailable(
        f"Lean not found; install elan and run `elan toolchain install "
        f"{LEAN_TOOLCHAIN}`, or pass --lean-bin")


def build_certificate(body: str, namespace: str) -> str:
    kernel = KERNEL_PATH.read_text()
    return (f"{kernel}\n{body}\n\n"
            f"-- runner-appended checks (fixed template)\n"
            f"example : _root_.DigCert.Safe {namespace}.prog := "
            f"{namespace}.{THEOREM}\n"
            f"#print axioms {namespace}.{THEOREM}\n")


def _precheck(body: str, namespace: str) -> str | None:
    if not _IDENT_RE.match(namespace):
        return f"invalid namespace {namespace!r}"
    for tok in BANNED_TOKENS:
        if re.search(rf"\b{re.escape(tok)}\b", body):
            return f"banned token {tok!r} in certificate body"
    if f"namespace {namespace}" not in body:
        return f"body does not declare namespace {namespace}"
    return None


def check_certificate(body: str, namespace: str, *,
                      lean_bin: str | None = None,
                      timeout: float = 60.0,
                      out_path: Path | str | None = None) -> LeanResult:
    """Check one certificate body. Never raises for Lean-side failures."""
    res = LeanResult(certified=False, status="error", namespace=namespace)
    why = _precheck(body, namespace)
    if why:
        res.status, res.reason = "rejected", why
        return res
    try:
        cmd, res.lean_version = resolve_lean(lean_bin)
    except LeanUnavailable as e:
        res.reason = str(e)
        return res

    text = build_certificate(body, namespace)
    if out_path is None:
        import tempfile
        out_path = Path(tempfile.mkdtemp(prefix="digcert_")) / "certificate.lean"
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(text)
    res.certificate_path = str(out_path)
    res.certificate_sha256 = hashlib.sha256(text.encode()).hexdigest()

    t0 = time.monotonic()
    try:
        # report every failing VC (Lean otherwise exits after 100 errors)
        p = subprocess.run([*cmd, "-DmaxErrors=1000000", str(out_path)],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        res.elapsed_sec = time.monotonic() - t0
        res.status, res.reason = "timeout", f"Lean exceeded {timeout}s"
        return res
    res.elapsed_sec = time.monotonic() - t0
    res.returncode = p.returncode
    res.output = out = p.stdout + p.stderr

    res.failed_tags = _FAILED_RE.findall(out)
    target = f"{namespace}.{THEOREM}"
    for name, axs in _AXIOMS_RE.findall(out):
        if name == target:
            res.axioms = [a.strip() for a in axs.split(",") if a.strip()]
    if any(name == target for name in _NO_AXIOMS_RE.findall(out)):
        res.axioms = []

    if res.failed_tags:
        res.status = "failed"
        res.reason = f"{len(res.failed_tags)} VC(s) failed"
    elif p.returncode != 0 or _ERROR_RE.search(out):
        res.status, res.reason = "error", "Lean reported errors"
    elif res.axioms is None:
        res.status, res.reason = "error", "no axiom report for theorem"
    elif not set(res.axioms) <= ALLOWED_AXIOMS:
        res.status = "rejected"
        res.reason = f"non-standard axioms: {sorted(set(res.axioms) - ALLOWED_AXIOMS)}"
    else:
        res.status, res.certified = "certified", True
    return res
