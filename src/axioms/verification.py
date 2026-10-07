"""Promotion of empirical findings through verifier plugins."""

from __future__ import annotations

from dataclasses import replace

from .engine import AxiomRun
from .evidence import Verdict
from .verify import FiniteDomainVerifier, ProofStatus, SmtModelVerifier


def apply_finite_verifier(run: AxiomRun, worker) -> AxiomRun:
    verifier = FiniteDomainVerifier()
    findings = []
    diagnostics = list(run.diagnostics)
    for finding in run.findings:
        if finding.verdict not in {Verdict.CANDIDATE, Verdict.VALIDATED}:
            findings.append(finding)
            continue
        result = verifier.verify(worker, run.manifest, finding.equation)
        if result.status is ProofStatus.PROVED:
            findings.append(
                replace(
                    finding,
                    verdict=Verdict.PROVED,
                    proof={
                        "verifier": result.verifier,
                        "version": result.version,
                        "scope": result.scope,
                        "assumptions": list(result.assumptions),
                        "artifact_digest": result.artifact_digest,
                    },
                )
            )
        elif result.status is ProofStatus.REFUTED:
            findings.append(
                replace(
                    finding,
                    verdict=Verdict.REFUTED,
                    counterexample=result.counterexample,
                )
            )
        elif result.status is ProofStatus.ERROR:
            findings.append(replace(finding, verdict=Verdict.ERROR))
        else:
            findings.append(finding)
            diagnostics.append(
                {
                    "severity": "info",
                    "code": "finite-verifier-unknown",
                    "message": f"{finding.id}: {result.detail or 'unsupported'}",
                }
            )
    return replace(run, findings=tuple(findings), diagnostics=tuple(diagnostics))


def apply_smt_model_verifier(run: AxiomRun) -> AxiomRun:
    verifier = SmtModelVerifier()
    findings = []
    diagnostics = list(run.diagnostics)
    for finding in run.findings:
        if finding.verdict not in {Verdict.CANDIDATE, Verdict.VALIDATED}:
            findings.append(finding)
            continue
        result = verifier.verify(run.manifest, finding.equation)
        if result.status is ProofStatus.PROVED:
            findings.append(
                replace(
                    finding,
                    verdict=Verdict.PROVED,
                    proof={
                        "verifier": result.verifier,
                        "version": result.version,
                        "scope": result.scope,
                        "assumptions": list(result.assumptions),
                        "artifact_digest": result.artifact_digest,
                    },
                )
            )
        elif result.status is ProofStatus.REFUTED:
            findings.append(
                replace(
                    finding,
                    verdict=Verdict.REFUTED,
                    counterexample=result.counterexample,
                )
            )
        elif result.status is ProofStatus.ERROR:
            findings.append(replace(finding, verdict=Verdict.ERROR))
        else:
            findings.append(finding)
            diagnostics.append(
                {
                    "severity": "info",
                    "code": "smt-model-verifier-unknown",
                    "message": f"{finding.id}: {result.detail or 'unsupported'}",
                }
            )
    return replace(run, findings=tuple(findings), diagnostics=tuple(diagnostics))
