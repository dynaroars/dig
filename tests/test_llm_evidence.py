"""Failed API calls must retain the request evidence without a real benchmark."""
import json
from pathlib import Path
import sys
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))
import llm_backend
import llm_infer


def test_failed_api_call_preserves_request_and_traces(monkeypatch, tmp_path):
    source = tmp_path / "test.c"
    source.write_text("void mainQ(int x) { vtrace1(x); }")
    class States(dict):
        exploration_info = {4: {"truncated": False}}
    dig = SimpleNamespace(tmpdir=tmp_path, inv_decls={"vtrace1": None},
                          symstates=States(vtrace1=[]))
    monkeypatch.setattr(llm_infer, "get_dig", lambda *a, **k: dig)
    def traces(dig, evidence):
        evidence["execution_traces"] = [{"input": {"x": "1"},
                                        "raw_trace_rows": ["vtrace1: 1"], "outcome": "traces"}]
        return "vtrace1: x=1"
    monkeypatch.setattr(llm_infer, "_trace_sample", traces)
    def fail(*a, **k):
        # The record must already be on disk when the network call begins.
        evidence = json.loads((tmp_path / "llm_evidence.json").read_text())
        assert "void mainQ" in evidence["rounds"][0]["prompt"]
        assert evidence["rounds"][0]["execution_traces"][0]["input"] == {"x": "1"}
        raise RuntimeError("mock API outage")
    monkeypatch.setattr(llm_backend, "generate", fail)
    with pytest.raises(RuntimeError, match="mock API outage"):
        llm_infer.run(source, seed=0, provider="gemini")
    evidence = json.loads((tmp_path / "llm_evidence.json").read_text())
    assert evidence["source_text"] == source.read_text()
    assert evidence["rounds"][0]["api_error"] is True
    assert evidence["rounds"][0]["api_elapsed_seconds"] >= 0
    assert evidence["rounds"][0]["trace_sample"] == "vtrace1: x=1"
    assert "response" not in evidence["rounds"][0]
    assert not (tmp_path / "llm_evidence.json.tmp").exists()


def test_candidates_skip_unexplored_locations():
    dig = SimpleNamespace(inv_decls={"vtrace1": None, "vtrace2": None},
                          symstates={"vtrace1": []})
    candidates = llm_infer._parse("x >= 0", dig)
    assert set(candidates) == {"vtrace1"}
