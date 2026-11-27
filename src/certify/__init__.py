"""Lean 4 certification of DIG loop invariants (see LEAN_CERTIFICATION_PLAN.md).

Trusted: `lean/DigCert.lean` (Stmt/Eval/Safe definitions), the C printer
`c_to_lean.py`, the invariant printer `inv_to_lean.py`, and the Lean kernel.
"""
from .emit_lean import CertifyReport, certify_c_program
from .runner import LeanResult, LeanUnavailable, check_certificate, resolve_lean

__all__ = ["CertifyReport", "LeanResult", "LeanUnavailable",
           "certify_c_program", "check_certificate", "resolve_lean"]
