"""M1 tests for the Lean certification kernel and runner.

Hand-written certificate bodies live in tests/certify_lean/. Skipped when no
Lean 4 toolchain is available.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "src"))

from certify import runner  # noqa: E402

FIX = Path(__file__).resolve().parent / "certify_lean"

try:
    LEAN_CMD, _ = runner.resolve_lean()
except runner.LeanUnavailable:
    LEAN_CMD = None

needs_lean = pytest.mark.skipif(LEAN_CMD is None, reason="Lean 4 not available")


def _check(name: str, ns: str, tmp_path: Path) -> runner.LeanResult:
    return runner.check_certificate((FIX / f"{name}.lean").read_text(), ns,
                                    out_path=tmp_path / f"{name}.lean")


@needs_lean
def test_kernel_compiles_without_sorry(tmp_path):
    f = tmp_path / "k.lean"
    f.write_text(runner.KERNEL_PATH.read_text() +
                 "\n#print axioms DigCert.wp_sound\n"
                 "#print axioms DigCert.safe_of_wp\n"
                 "#print axioms DigCert.cdiv_eq\n")
    p = subprocess.run([*LEAN_CMD, str(f)], capture_output=True, text=True,
                       timeout=120)
    assert p.returncode == 0, p.stdout + p.stderr
    assert "sorryAx" not in p.stdout
    assert p.stdout.count("depends on axioms") + \
        p.stdout.count("does not depend on any axioms") == 3


@needs_lean
def test_semantics_not_vacuous(tmp_path):
    """Proved in Lean: programs with a reachable failing check (including in
    a non-terminating loop) are not Safe."""
    f = tmp_path / "nv.lean"
    f.write_text(runner.KERNEL_PATH.read_text() + "\n" +
                 (FIX / "nonvacuous.lean").read_text() +
                 "\n#print axioms Cert_nonvacuous.nonterminating_unsafe\n")
    p = subprocess.run([*LEAN_CMD, str(f)], capture_output=True, text=True,
                       timeout=120)
    assert p.returncode == 0, p.stdout + p.stderr
    assert "sorryAx" not in p.stdout


@needs_lean
def test_ps2_certifies(tmp_path):
    r = _check("ps2", "Cert_ps2", tmp_path)
    assert r.certified, (r.status, r.reason, r.output)
    assert set(r.axioms) <= runner.ALLOWED_AXIOMS
    assert r.certificate_sha256 and len(r.certificate_sha256) == 64


@needs_lean
def test_cohendiv_nested_certifies(tmp_path):
    r = _check("cohendiv", "Cert_cohendiv", tmp_path)
    assert r.certified, (r.status, r.reason, r.output)


@needs_lean
def test_false_invariant_rejected(tmp_path):
    r = _check("ps2_false_inv", "Cert_ps2_bad", tmp_path)
    assert not r.certified
    assert r.status == "failed"
    assert set(r.failed_tags) == {"vtrace1.bad"}
    assert "sorryAx" in r.axioms


@needs_lean
def test_nonterminating_noninductive_rejected(tmp_path):
    r = _check("nonterminating_false", "Cert_nonterm_bad", tmp_path)
    assert not r.certified
    assert r.failed_tags == ["vtrace1.0"]


@needs_lean
def test_shadowed_safe_rejected(tmp_path):
    """A body that redefines `Safe` locally must not pass the fixed-template
    statement check."""
    body = (FIX / "ps2.lean").read_text().replace(
        "theorem mainQ_certified : Safe prog := by\n  unfold prog inv1\n  dig_vcs",
        "def Safe (_ : Stmt State) : Prop := True\n"
        "theorem mainQ_certified : Safe prog := trivial")
    assert "def Safe" in body
    r = runner.check_certificate(body, "Cert_ps2", out_path=tmp_path / "s.lean")
    assert not r.certified
    assert r.status == "error"


@pytest.mark.parametrize("tok", ["sorry", "admit", "axiom", "native_decide"])
def test_banned_tokens_rejected_without_lean(tok):
    body = (FIX / "ps2.lean").read_text() + f"\n-- {tok}\n"
    r = runner.check_certificate(body, "Cert_ps2")
    assert r.status == "rejected" and not r.certified


def _run_snippet(tmp_path: Path, body: str) -> str:
    f = tmp_path / "snip.lean"
    f.write_text(runner.KERNEL_PATH.read_text() + "\nnamespace T\nopen DigCert\n"
                 + body + "\nend T\n")
    p = subprocess.run([*LEAN_CMD, str(f)], capture_output=True, text=True,
                       timeout=120)
    return p.stdout + p.stderr


@needs_lean
def test_conjunctive_tag_keeps_attribution(tmp_path):
    """`Tag` is irreducible: dig_vcs's `apply And.intro` must not split a
    tagged conjunction, so a failure is reported under its own tag."""
    out = _run_snippet(tmp_path, """
example (a b : Int) (h : a = 1) (h2 : b = 2) : Tag "conj" (a = 1 ∧ b = 3) := by
  repeat' (first | apply And.intro | intro _)
  dig_discharge
""")
    assert "DIG_VC_FAILED conj" in out
    assert "DIG_VC_FAILED untagged" not in out


@needs_lean
def test_c_division_discharged(tmp_path):
    out = _run_snippet(tmp_path, """
example (r y : Int) (hy : y ≥ 1) (hr : r ≥ 0) :
    Tag "d1" (cdiv r y * y + cmod r y = r) := by dig_discharge
example (r : Int) (hr : r < 0) : Tag "d2" (cdiv r 2 ≤ 0) := by dig_discharge
example (r : Int) : Tag "d3" (cdiv (-7) 2 = -3 ∧ cmod (-7) 2 = -1) := by
  dig_discharge
""")
    assert "DIG_VC_FAILED" not in out, out
    assert ": error" not in out, out


# ── M2: C → Lean translation, invariant printing, end-to-end certification ──

import sympy  # noqa: E402
import z3  # noqa: E402

from certify.c_to_lean import CProgram, Unsupported  # noqa: E402
from certify.emit_lean import certify_c_program  # noqa: E402
from certify.inv_to_lean import UnsupportedInv, to_lean  # noqa: E402

NLA = Path(__file__).resolve().parent.parent / "benchmark" / "c" / "nla"


def _eqt(s: str):
    from infer.eqt import Eqt
    return Eqt(sympy.Eq(sympy.sympify(s), 0))


def _oct(lhs: str, rhs: int):
    from infer.oct import Oct
    return Oct(sympy.Le(sympy.sympify(lhs), rhs))


def test_translate_ps2_structure():
    cp = CProgram(NLA / "ps2.c")
    assert cp.vars == ["k", "y", "x", "c"]
    assert len(cp.loops) == 1 and cp.loops[0].head_loc == "vtrace1"
    assert cp.loops[0].trivial_guard
    assert cp.loops[0].writes == {"c", "y", "x"}
    assert [s.loc for s in cp.sites] == ["vtrace1"]
    assert cp.sites[0].args == {"x": "s.v_x", "y": "s.v_y", "k": "s.v_k"}


def test_translate_nested_and_real_guard():
    cp = CProgram(NLA / "cohendiv.c")
    assert [lp.parent for lp in cp.loops] == [None, 0]
    assert cp.loops[1].writes == {"a", "b"}
    cp = CProgram(NLA / "isqrt.c")
    assert not cp.loops[0].trivial_guard
    # vtrace1 at the loop head and again after the loop
    assert [(s.loc, s.loop) for s in cp.sites] == [("vtrace1", 0), ("vtrace1", None)]


def test_division_emits_nonzero_check():
    cp = CProgram(NLA / "dijkstra.c")
    prog = cp.render_prog()
    assert "cdiv" in prog and 'Tag "div@' in prog


@pytest.mark.parametrize("prog", ["freire2"])
def test_floats_unsupported(prog):
    with pytest.raises(Unsupported):
        CProgram(NLA / f"{prog}.c")


def test_unsupported_c_constructs(tmp_path):
    cases = {
        "ptr": "int mainQ(int x){ int *p; return 0; }",
        "global": "int g; int mainQ(int x){ return x; }",
        "shadow": "int mainQ(int x){ { int x = 1; } return x; }",
        "unsigned": "int mainQ(unsigned x){ return 0; }",
        "call": "int f(int a){return a;} int mainQ(int x){ x = f(x); return x; }",
    }
    for name, src in cases.items():
        f = tmp_path / f"{name}.c"
        f.write_text(src)
        with pytest.raises(Unsupported):
            CProgram(f)


def test_inv_to_lean_ops():
    x, y = z3.Ints("x y")
    env = {"x": "s.v_x", "y": "s.v_y"}
    assert to_lean(x * y - 2 * x == 0, env) == "(((s.v_x * s.v_y) - (2 * s.v_x)) = 0)"
    ite = to_lean(z3.If(x >= y, x <= 3, y <= 3), env)
    assert "→" in ite and "¬" in ite
    assert to_lean(x % 2 == 1, env) == "((s.v_x % 2) = 1)"
    with pytest.raises(UnsupportedInv):
        to_lean(x % y == 0, env)                 # divisor not a numeral
    with pytest.raises(UnsupportedInv):
        to_lean(z3.Int("w") == 0, env)           # unbound variable
    with pytest.raises(UnsupportedInv):
        to_lean(z3.Real("r") == 0, {"r": "s.v_r"})


@needs_lean
def test_e2e_ps2_drops_false_invariant(tmp_path):
    # -x - y <= 0 alone is not inductive (y = -3, x = 3 breaks it); -y <= 0
    # supports it, as Houdini-style candidates must.
    dinvs = {"vtrace1": [_eqt("2*x - y**2 - y"), _oct("-x - y", 0),
                         _oct("-y", 0), _eqt("x - y - 999")]}
    rep = certify_c_program(NLA / "ps2.c", dinvs, out_path=tmp_path / "c.lean")
    certified = {c["text"] for c in rep.certified}
    assert certified == {"2*x - y**2 - y == 0", "-x - y <= 0", "-y <= 0"}, \
        rep.summary()
    assert [d["text"] for d in rep.dropped] == ["x - y - 999 == 0"]
    assert rep.status == "partial"


@needs_lean
def test_e2e_cohendiv_nested(tmp_path):
    inner = ["q*y + r - x", "a*y - b"]
    dinvs = {"vtrace1": [_eqt(e) for e in inner] + [_oct("-r", 0)],
             "vtrace2": [_eqt(e) for e in inner] + [_oct("b - r", 0)]}
    rep = certify_c_program(NLA / "cohendiv.c", dinvs, out_path=tmp_path / "c.lean")
    assert rep.status == "certified", (rep.summary(), rep.round_log)
    assert len(rep.certified) == 6


@needs_lean
def test_e2e_real_guard_and_post_loop_vtrace(tmp_path):
    # isqrt: while ((r+1)*(r+1) <= n) { vtrace1(n, r); r++; } vtrace1(n, r);
    dinvs = {"vtrace1": [_oct("r*r - n", 0), _oct("-r", 0)]}
    rep = certify_c_program(NLA / "isqrt.c", dinvs, out_path=tmp_path / "c.lean")
    assert rep.status == "certified", (rep.summary(), rep.round_log)


@needs_lean
def test_e2e_vtrace_not_at_head_is_not_certified_vacuously(tmp_path):
    f = tmp_path / "mid.c"
    f.write_text("""
void vassume(int b){}
void vtrace1(int i, int n){}
int mainQ(int n){
  vassume(n >= 0);
  int i = 0;
  while (i < n) {
    i = i + 1;
    if (i > 2) { vtrace1(i, n); }
  }
  return i;
}""")
    # i <= n holds at the vtrace but the loop has no head invariant, and
    # i >= 100 is false: neither may be certified from nothing.
    dinvs = {"vtrace1": [_oct("i - n", 0), _oct("-i", -100)]}
    rep = certify_c_program(f, dinvs, out_path=tmp_path / "c.lean")
    assert not any(c["text"] == "-i <= -100" for c in rep.certified)
    assert rep.status in ("partial", "failed")


# ── M3: loop frames (checked by Lean, so untrusted) ──

@needs_lean
def test_assume_frame_fact_supports_loop(tmp_path):
    f = tmp_path / "frame.c"
    f.write_text("""
void vassume(int b){}
void vtrace1(int x, int k){}
int mainQ(int k){
  vassume(k >= 0);
  int x = 0;
  while (1) {
    vtrace1(x, k);
    if (!(x < 10)) break;
    x = x + k;
  }
  return x;
}""")
    # x >= 0 is only inductive given k >= 0, which no candidate states.
    rep = certify_c_program(f, {"vtrace1": [_oct("-x", 0)]},
                            out_path=tmp_path / "c.lean")
    assert rep.status == "certified", (rep.summary(), rep.round_log)
    assert "k" in rep.loops[0]["frame"]


@needs_lean
def test_outer_candidate_frames_inner_loop(tmp_path):
    f = tmp_path / "nest.c"
    f.write_text("""
void vassume(int b){}
void vtrace1(int i, int n){}
void vtrace2(int j, int i, int n){}
int mainQ(int n){
  vassume(n >= 1);
  int i = 0;
  int j;
  while (1) {
    vtrace1(i, n);
    if (!(i < n)) break;
    j = 0;
    while (1) {
      vtrace2(j, i, n);
      if (!(j < i)) break;
      j = j + 1;
    }
    i = i + 1;
  }
  return i;
}""")
    # inner claim j <= n needs i <= n, which only the outer loop states
    dinvs = {"vtrace1": [_oct("i - n", 0)], "vtrace2": [_oct("j - n", 0)]}
    rep = certify_c_program(f, dinvs, out_path=tmp_path / "c.lean")
    assert rep.status == "certified", (rep.summary(), rep.round_log)
    assert set(rep.loops[1]["frame"]) == {"i", "n"}


@needs_lean
def test_invalidated_assume_is_not_trusted(tmp_path):
    f = tmp_path / "bad_aux.c"
    # the assumed fact is invalidated before the loop: the frame carries
    # k == -1, so the claim k >= 0 must not be certified
    f.write_text("""
void vassume(int b){}
void vtrace1(int x, int k){}
int mainQ(int k){
  vassume(k >= 0);
  k = -1;
  int x = 0;
  while (1) {
    vtrace1(x, k);
    if (!(x < 10)) break;
    x = x + 1;
    x = x + k;
  }
  return x;
}""")
    rep = certify_c_program(f, {"vtrace1": [_oct("-k", 0)]},
                            out_path=tmp_path / "c.lean")
    assert rep.certified == []


def test_short_circuit_division_checks_are_guarded(tmp_path):
    f = tmp_path / "sc.c"
    f.write_text("""
void vtrace1(int x, int y);
int mainQ(int x, int y){
  int z = 0;
  if (y != 0 && x / y > 1) { z = 1; }
  z = (y == 0) ? 0 : x % y;
  vtrace1(x, y);
  return x / 1;
}""")
    cp = CProgram(f)            # prototype-only vtrace accepted
    assert cp.vtrace_params == {"vtrace1": ["x", "y"]}
    prog = cp.render_prog()
    assert 'Tag "div@5" ((s.v_y ≠ 0) → (s.v_y ≠ 0))' in prog      # &&
    assert 'Tag "div@6" ((¬ (s.v_y = 0)) → (s.v_y ≠ 0))' in prog   # ?:
    assert 'Tag "div@' in prog.split(".ret")[0]   # return x / 1 checked


@needs_lean
def test_short_circuit_division_certifies(tmp_path):
    f = tmp_path / "sc2.c"
    f.write_text("""
void vtrace1(int z);
int mainQ(int x, int y){
  int z = 0;
  if (y != 0 && x / y > 1) { z = 1; }
  z = (y == 0) ? 0 : x % y;
  vtrace1(z);
  return z;
}""")
    rep = certify_c_program(f, {"vtrace1": []}, out_path=tmp_path / "c.lean")
    assert rep.round_log[-1]["status"] == "certified", rep.round_log


# ── M4: CLI / pipeline wiring ──

@needs_lean
def test_cli_certify_lean_end_to_end(tmp_path):
    """dig.py --z3-check --certify-lean on ps2 (report-only Lean pass over
    z3-checked invariants): prints the certification summary, writes
    the certificate and the JSON report, and records it in evidence.json.
    (A single DIG invocation; benchmark runs must stay serial.)"""
    import json
    root = Path(__file__).resolve().parent.parent
    out = tmp_path / "ps2_cert.lean"
    p = subprocess.run(
        [sys.executable, "-O", "dig.py", str(NLA / "ps2.c"), "-seed", "1",
         "-tmpdir", str(tmp_path), "--z3-check", "--certify-lean",
         "--lean-out", str(out)],
        cwd=root / "src", capture_output=True, text=True, timeout=600)
    assert p.returncode == 0, p.stdout + p.stderr
    assert "lean-cert ps2:" in p.stdout
    assert "certified vtrace1: 2*x - y**2 - y == 0" in p.stdout
    assert out.is_file() and "theorem mainQ_certified" in out.read_text()
    run = next(d for d in tmp_path.iterdir() if d.is_dir())
    rep = json.loads((run / "lean_certification.json").read_text())
    assert rep["status"] in ("certified", "partial")
    ev = json.loads((run / "evidence.json").read_text())
    assert ev["lean_certification"]["certificate_sha256"] == rep["certificate_sha256"]


def test_cli_defaults():
    import settings
    assert settings.DO_CERTIFY_LEAN is False      # opt-in Lean certification pass
    assert settings.VERIFIER == "z3"              # default verifier for C
    assert settings.LEAN_KEEP_UNVERIFIED is False


@needs_lean
def test_cli_lean_only_verifier(tmp_path):
    """--lean-only mode on cohendiv: candidates are not z3-checked; Lean proves
    what is reported and drops the rest (trace artifacts such as bounds that
    only hold on the sampled inputs)."""
    import json
    root = Path(__file__).resolve().parent.parent
    p = subprocess.run(
        [sys.executable, "-O", "dig.py", str(NLA / "cohendiv.c"), "-seed", "42",
         "-tmpdir", str(tmp_path), "--lean-only"],
        cwd=root / "src", capture_output=True, text=True, timeout=900)
    assert p.returncode == 0, p.stdout + p.stderr
    assert "verifier: Lean" in p.stderr
    assert "lean-cert cohendiv:" in p.stdout
    assert "q*y + r - x == 0" in p.stdout
    run = next(d for d in tmp_path.iterdir() if d.is_dir())
    rep = json.loads((run / "lean_certification.json").read_text())
    assert rep["certified"] and rep["dropped"]
    reported = {(c["loc"], c["text"]) for c in rep["certified"]}
    dropped = {(c["loc"], c["text"]) for c in rep["dropped"]}
    # every reported invariant is Lean-certified; nothing dropped is reported
    for loc, text in dropped:
        assert text not in p.stdout.split(f"{loc} (")[-1].split("\nvtrace")[0]
    assert len(reported) == int(p.stdout.split(" invs ")[1].split()[0])


@needs_lean
def test_extra_helpers_support_but_are_not_claimed(tmp_path):
    # ps2: 2x = y^2 + y is inductive alone; x >= y needs y >= 0 as support,
    # supplied only as an extra (pre-simplify) helper.
    dinvs = {"vtrace1": [_oct("y - x", 0)]}
    extra = {"vtrace1": [_oct("-y", 0), _eqt("2*x - y**2 - y"), _oct("y - x", 0)]}
    rep = certify_c_program(NLA / "ps2.c", dinvs, out_path=tmp_path / "c.lean",
                            extra_helpers=extra)
    assert [c["text"] for c in rep.certified] == [str(dinvs["vtrace1"][0])], rep.round_log
    assert rep.status == "certified"
    rep0 = certify_c_program(NLA / "ps2.c", dinvs, out_path=tmp_path / "d.lean")
    assert rep0.certified == []
