"""Counterexample inputs refer to entry values, including unobserved inputs."""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from data.prog import DSymbs, Symb, Symbs
from data.symstates import SymStates, SymStatesMakerC
from data.traces import Inps
from infer.inv import DInvs
import settings


def make_states(tmp_path, monkeypatch, parameters, body):
    source = tmp_path / "inputs.c"
    source.write_text(f"void vtrace(int x) {{}} void mainQ({parameters}) {{{body}}}")
    inputs = Symbs([Symb(parameter.split()[-1], "I") for parameter in parameters.split(",")])
    states = SymStates(inputs, DSymbs({"vtrace": Symbs([Symb("x", "I")])}))
    monkeypatch.setattr(settings, "SE_MAX_DEPTH", 2)
    states.compute(SymStatesMakerC, source, "mainQ", "inputs", tmp_path)
    return states


def generated_inputs(states, cexs):
    return Inps().merge(cexs, states.inp_decls.names,
                        model_ss=tuple(map(str, states.inp_exprs)))


def test_mutated_and_unused_inputs_are_replayed_from_entry_values(tmp_path, monkeypatch):
    states = make_states(tmp_path, monkeypatch, "int x, int unused",
                         "vassume(x == 5); x++; vtrace(x);")
    cexs, _ = states.check(DInvs.mk_false_invs(["vtrace"]), None)
    inputs = generated_inputs(states, cexs)
    assert len(inputs) == 1
    assert next(iter(inputs)).vs == (5, 0)
    assert next(iter(cexs["vtrace"].values()))[0]["x"] == 6


def test_exclusion_blocks_entry_value_after_mutation(tmp_path, monkeypatch):
    states = make_states(tmp_path, monkeypatch, "int x",
                         "vassume(x == 5); x++; vtrace(x);")
    cexs, _ = states.check(DInvs.mk_false_invs(["vtrace"]), None)
    inputs = generated_inputs(states, cexs)
    assert next(iter(inputs)).vs == (5,)
    after, _ = states.check(DInvs.mk_false_invs(["vtrace"]), inputs)
    assert after == {}
