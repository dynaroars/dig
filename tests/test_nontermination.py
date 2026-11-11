"""Inputs the program never finishes on must be reported, not just dropped.

A run that exhausts settings.C.RUN_TIMEOUT is killed and its traces discarded.
These tests check that the user is told, that a provable divergence is named as
such with a witness, that an unprovable one is reported as a suspicion only,
and that a program which terminates pays nothing.
"""
import logging
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

import data.prog as dprog
from data.prog import C, Prog
from data.traces import Inp, Inps
import settings


def build(tmp_path, body, name="nt"):
    """Compile a one-input program whose loop body is `body`."""
    source = tmp_path / f"{name}.c"
    source.write_text(f"""
        #include <stdio.h>
        #include <stdlib.h>
        void vassume(int b){{}}
        void vtrace1(int x, int i){{}}
        int mainQ(int x){{
            int i = 0;
            {body}
            vtrace1(x, i);
            return i;
        }}
        int main(int argc, char **argv){{ mainQ(atoi(argv[1])); return 0; }}
    """)
    work = tmp_path / f"work_{name}"
    work.mkdir()
    compiled = C(source, work)
    return Prog(str(compiled.traceexe), compiled.inp_decls,
                compiled.inv_decls, source=source)


def collect(prog, values):
    return prog._get_traces_mp(Inps([Inp(("x",), (v,)) for v in values]))


def test_provable_divergence_is_named_with_a_witness(tmp_path, monkeypatch, caplog):
    """`while (x > 0) { i = 1 - i; }` runs forever for every positive x, and
    the engine can prove it, so say so rather than leaving the user to wonder
    why the traces vanished."""
    monkeypatch.setattr(settings, "DO_MP", False)
    monkeypatch.setattr(settings.C, "RUN_TIMEOUT", 1)
    prog = build(tmp_path, "while (x > 0) { i = 1 - i; }", name="diverging")

    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        collect(prog, [5])

    assert prog.execution_outcomes[Inp(("x",), (5,))] == "timeout"
    errors = [r.message for r in caplog.records if r.levelno >= logging.ERROR]
    assert errors, caplog.text
    assert "does not terminate" in errors[0]
    assert "loop #0" in errors[0]
    assert "x=" in errors[0]              # the proof's witness input
    loop, witness = prog.nontermination
    assert loop == 0 and witness and int(witness["x"]) > 0


def test_unprovable_timeout_is_a_suspicion_not_a_proof(tmp_path, monkeypatch, caplog):
    """`while (i != x) { i = (i + 2) % 1000000; }` never finishes for odd x,
    but neither proof engine covers it. The report must not claim it does."""
    monkeypatch.setattr(settings, "DO_MP", False)
    monkeypatch.setattr(settings.C, "RUN_TIMEOUT", 1)
    prog = build(tmp_path, "while (i != x) { i = (i + 2) % 1000000; }",
                 name="unprovable")

    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        collect(prog, [7])

    assert prog.execution_outcomes[Inp(("x",), (7,))] == "timeout"
    assert prog.nontermination == (None, None)
    msgs = [r.message for r in caplog.records]
    assert any("may not terminate" in m for m in msgs), caplog.text
    assert not any("does not terminate" in m for m in msgs), caplog.text


def test_terminating_program_reports_nothing_and_skips_the_proof(tmp_path, monkeypatch, caplog):
    """No timeout, no report -- and the proof is never attempted, so programs
    that finish pay nothing for this check."""
    monkeypatch.setattr(settings, "DO_MP", False)
    monkeypatch.setattr(settings.C, "RUN_TIMEOUT", 1)
    attempts = []
    original = dprog._nontermination_of

    def spy(text, filename):
        attempts.append(filename)
        return original(text, filename)

    monkeypatch.setattr(dprog, "_nontermination_of", spy)
    prog = build(tmp_path, "while (i < x) { i = i + 1; }", name="terminating")

    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        traces = collect(prog, [3, 4])

    assert all(traces.values())
    assert not attempts, "the proof was attempted although nothing timed out"
    msgs = [r.message for r in caplog.records]
    assert not any("terminate" in m for m in msgs), caplog.text


def test_each_timing_out_input_is_reported_once(tmp_path, monkeypatch, caplog):
    """Repeated batches must not re-report inputs already named."""
    monkeypatch.setattr(settings, "DO_MP", False)
    monkeypatch.setattr(settings.C, "RUN_TIMEOUT", 1)
    prog = build(tmp_path, "while (x > 0) { i = 1 - i; }", name="once")

    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        collect(prog, [5])
        first = len([r for r in caplog.records if "does not terminate" in r.message])
        collect(prog, [6])
        second = len([r for r in caplog.records if "does not terminate" in r.message])

    assert first == 1, caplog.text
    # the second batch brings a new input, so exactly one more report
    assert second == 2, caplog.text
    prog._report_nontermination()
    again = len([r for r in caplog.records if "does not terminate" in r.message])
    assert again == 2, "nothing new, yet it reported again"


def test_report_survives_an_unreadable_source(tmp_path, monkeypatch, caplog):
    """Losing the source must not lose the diagnostic: the timeouts are still
    reported, just without a proof."""
    monkeypatch.setattr(settings, "DO_MP", False)
    monkeypatch.setattr(settings.C, "RUN_TIMEOUT", 1)
    prog = build(tmp_path, "while (x > 0) { i = 1 - i; }", name="gone")
    (tmp_path / "gone.c").unlink()

    with caplog.at_level(logging.DEBUG, logger="data.prog"):
        collect(prog, [5])

    assert prog.nontermination == (None, None)
    assert any("may not terminate" in r.message for r in caplog.records), caplog.text
