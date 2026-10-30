"""Human and stable JSON rendering for axiom runs."""

from __future__ import annotations

import json

from .engine import AxiomRun
from .model import format_equation


def render_json(run: AxiomRun) -> str:
    return json.dumps(
        run.to_data(), ensure_ascii=False, allow_nan=False, indent=2, sort_keys=True
    ) + "\n"


def render_text(run: AxiomRun) -> str:
    lines = [
        f"axiom analysis: {run.manifest.language} {run.target_fingerprint}",
        f"terms: {len(run.enumeration.terms)}; findings: {len(run.findings)}",
    ]
    for finding in run.findings:
        lines.append(f"{finding.verdict.value} {format_equation(finding.equation)}")
        lines.append(
            "  discovery: "
            f"{finding.discovery.valid} valid, "
            f"{finding.discovery.invalid_domain} invalid-domain"
        )
        lines.append(
            "  validation: "
            f"{finding.validation.valid} valid, "
            f"{finding.validation.invalid_domain} invalid-domain, "
            f"{finding.validation.failed} failed"
        )
        if finding.proof:
            lines.append(
                f"  proof: {finding.proof['verifier']} {finding.proof['version']} "
                f"({finding.proof['scope']})"
            )
        else:
            lines.append("  proof: none")
    for diagnostic in run.diagnostics:
        lines.append(
            f"{diagnostic['severity'].upper()} {diagnostic['code']}: {diagnostic['message']}"
        )
    return "\n".join(lines) + "\n"
