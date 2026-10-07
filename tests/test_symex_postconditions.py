"""Postconditions after concrete tails of symbolic loops remain reachable."""
import sys
from pathlib import Path

import pytest
import z3

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))
from data.symex_c import CSymEx


@pytest.mark.parametrize("name", ["cav09_fig1a", "cav09_fig1d"])
def test_complexity_postconditions_at_shallow_depth(name):
    source = Path(__file__).resolve().parent.parent / "benchmark/c/complexity" / (name+".c")
    engine = CSymEx(source, 4)
    records = engine.run()
    assert records
    assert len(records) < 20
    target = engine.parse_c_expr("m*tCtr-tCtr*tCtr-100*m+200*tCtr-10000 == 0")
    # Every explored postcondition satisfies the published polynomial bound.
    assert engine.check_inv("vtrace_post", target)[0] == "valid"


def test_symbolic_body_does_not_evade_concrete_guard_budget(tmp_path):
    source = tmp_path / "branching.c"
    source.write_text("void vtrace(int x, int y){} void mainQ(int m) {"
                      "int x=0,y=0; while(x<3){if(y<m)y++;else x++;}vtrace(x,y);}")
    engine = CSymEx(source, 2)
    records = engine.run()
    assert records
    assert len(records) <= 3
    assert engine._incomplete
