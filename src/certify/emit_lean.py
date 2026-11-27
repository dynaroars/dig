"""Emit Lean certificates for DIG invariants and run the drop pass.

Tags (all parsed back from `DIG_VC_FAILED <tag>`):
  * `<loc>.<k>`    — the check of candidate k at every `<loc>` vtrace call
                     (the property being certified);
  * `<loc>.<k>@h`  — candidate k used as a loop-head invariant conjunct;
  * `<loc>.<k>@g`  — `guard → candidate k` as a loop-head conjunct (only
                     for loops with a real guard `while (c) { vtrace; … }`);
Frames: each loop carries the fields it never writes; `wp` gives the body
and the loop exit the facts that those fields equal their values at loop
entry (so `vassume` facts, enclosing-loop invariants and path conditions
over unwritten variables survive the loop). Lean proves the frame is
preserved, so the frame computation is untrusted.
Head conjuncts are helpers: dropping one only weakens the induction. A
failing check drops candidate k at `<loc>` entirely (check and helpers),
Houdini-style, and the certificate is regenerated until Lean accepts it or
the round cap is reached (then the run is reported as not certified).
"""

import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

from .c_to_lean import CProgram, Loop, Site, Unsupported
from .inv_to_lean import UnsupportedInv, inv_to_lean
from .runner import LeanResult, check_certificate

# Per-VC heartbeat budget (thousands) by certificate size (tagged conjuncts).
# Budget never affects soundness, only how hard each VC is tried; very large
# certificates (egcd2/egcd3) need smaller budgets to finish in reasonable time.
VC_BUDGETS = ((150, None), (250, 25000), (10**9, 10000))   # (max tags, budget)


@dataclass
class Candidate:
    loc: str
    k: int
    text: str
    kind: str
    dig_stat: str | None


@dataclass
class CertifyReport:
    status: str                       # certified | partial | failed | unsupported | error
    program: str
    reason: str | None = None
    rounds: int = 0
    total_elapsed_sec: float = 0.0
    lean_elapsed_sec: float = 0.0
    lean_version: str | None = None
    certificate_path: str | None = None
    certificate_sha256: str | None = None
    certified: list[dict] = field(default_factory=list)
    dropped: list[dict] = field(default_factory=list)
    unsupported: list[dict] = field(default_factory=list)
    loops: list[dict] = field(default_factory=list)
    round_log: list[dict] = field(default_factory=list)

    def to_dict(self) -> dict:
        return asdict(self)

    def summary(self) -> str:
        n_c, n_d, n_u = len(self.certified), len(self.dropped), len(self.unsupported)
        return (f"lean-cert {self.program}: {self.status}; certified {n_c}, "
                f"dropped {n_d}, unsupported {n_u}; {self.rounds} round(s), "
                f"Lean {self.lean_elapsed_sec:.1f}s"
                + (f" ({self.reason})" if self.reason else ""))


def _namespace(cfile: Path) -> str:
    base = "".join(ch if ch.isalnum() else "_" for ch in cfile.stem)
    return f"Cert_{base}"


def _inv_kind(inv) -> str:
    return type(inv).__name__


class Certifier:
    def __init__(self, cfile: Path | str, dinvs, *, lean_bin: str | None = None,
                 timeout: float = 120.0, max_rounds: int = 8,
                 out_path: Path | str | None = None, extra_helpers=None):
        self.cfile = Path(cfile)
        self.ns = _namespace(self.cfile)
        self.lean_bin, self.timeout, self.max_rounds = lean_bin, timeout, max_rounds
        self.out_path = out_path
        self.report = CertifyReport(status="error", program=self.cfile.stem)
        self.budget_cap: int | None = None     # lowered after a Lean timeout
        try:
            self.cp = CProgram(self.cfile)
        except Unsupported as e:
            self.cp = None
            self.report.status, self.report.reason = "unsupported", f"C: {e}"
            return

        # candidates per location, in a stable order
        self.cands: dict[tuple[str, int], Candidate] = {}
        self.lean: dict[tuple[tuple[str, int], int], str] = {}  # ((loc,k), site#) -> Prop
        self.invs: dict[tuple[str, int], object] = {}
        sites_by_loc: dict[str, list[tuple[int, Site]]] = {}
        for i, site in enumerate(self.cp.sites):
            sites_by_loc.setdefault(site.loc, []).append((i, site))
        for loc in sorted(dinvs.keys()):
            invs = sorted(dinvs[loc], key=str)
            for k, inv in enumerate(invs):
                key = (loc, k)
                cand = Candidate(loc, k, str(inv), _inv_kind(inv),
                                 str(inv.stat) if inv.stat else None)
                if loc not in sites_by_loc:
                    self.report.unsupported.append(
                        {**asdict(cand), "reason": "no vtrace call for location"})
                    continue
                try:
                    for i, site in sites_by_loc[loc]:
                        self.lean[(key, i)] = inv_to_lean(inv, site.args)
                except UnsupportedInv as e:
                    self.report.unsupported.append({**asdict(cand), "reason": str(e)})
                    continue
                self.cands[key] = cand
                self.invs[key] = inv
        # Extra helper-only candidates (e.g. DIG's pre-`simplify` invariants):
        # loop-head conjuncts that may support induction but are never
        # reported as certified. Keys use ("<loc>", "x<k>").
        self.xhelpers: dict[tuple[str, str], str] = {}
        if extra_helpers:
            claimed = {(c.loc, c.text) for c in self.cands.values()}
            for loc in sorted(extra_helpers.keys()):
                heads = [(lp, s) for lp in self.cp.loops for s in self.cp.sites
                         if lp.head_loc == loc and s.loc == loc and s.loop == lp.idx]
                if not heads:
                    continue
                for k, inv in enumerate(sorted(extra_helpers[loc], key=str)):
                    if (loc, str(inv)) in claimed:
                        continue
                    try:
                        self.xhelpers[(loc, f"x{k}")] = inv_to_lean(inv, heads[0][1].args)
                    except UnsupportedInv:
                        pass
        self.active = set(self.cands)
        self.helpers = set()           # (key, "h"|"g")
        for lp in self.cp.loops:
            if lp.head_loc is None:
                continue
            for key in self.cands:
                if key[0] == lp.head_loc:
                    self.helpers.add((key, "h"))
                    if not lp.trivial_guard:
                        self.helpers.add((key, "g"))
            for key in self.xhelpers:
                if key[0] == lp.head_loc:
                    self.helpers.add((key, "h"))
                    if not lp.trivial_guard:
                        self.helpers.add((key, "g"))

    # ── rendering ─────────────────────────────────────────────────────
    def _checks(self, site: Site) -> list[tuple[str, str]]:
        out = []
        for key in sorted(self.active):
            if key[0] != site.loc:
                continue
            prop = self._lookup(key, site)
            out.append((f"{key[0]}.{key[1]}", prop))
        return out

    def _lookup(self, key, site: Site) -> str:
        # sites are re-created during rendering; match by (loc, args)
        for (k2, i), prop in self.lean.items():
            if k2 == key and self.cp.sites[i].args == site.args:
                return prop
        raise KeyError((key, site))

    def _head(self, lp: Loop) -> list[tuple[str, str]]:
        if lp.head_loc is None:
            return []
        head_site = next((s for s in self.cp.sites
                          if s.loc == lp.head_loc and s.loop == lp.idx), None)
        if head_site is None:
            return []
        out = []
        for key in sorted(self.active):
            if key[0] != lp.head_loc:
                continue
            prop = self._lookup(key, head_site)
            tag = f"{key[0]}.{key[1]}"
            if (key, "h") in self.helpers:
                out.append((f"{tag}@h", prop))
            if (key, "g") in self.helpers:
                out.append((f"{tag}@g", f"({lp.guard} → {prop})"))
        for key, prop in sorted(self.xhelpers.items()):
            if key[0] != lp.head_loc:
                continue
            tag = f"{key[0]}.{key[1]}"
            if (key, "h") in self.helpers:
                out.append((f"{tag}@h", prop))
            if (key, "g") in self.helpers:
                out.append((f"{tag}@g", f"({lp.guard} → {prop})"))
        return out

    def body(self) -> str:
        prog = self.cp.render_prog(self._checks, self._head)
        prog = "\n".join("  " + ln for ln in prog.splitlines())
        # Large certificates: lower per-VC budget so non-inductive conjuncts
        # fail fast (budget never affects soundness, only completeness).
        n_tags = prog.count('Tag "')
        self.n_tags = n_tags
        hb = next(b for lim, b in VC_BUDGETS if n_tags <= lim)
        if self.budget_cap is not None:
            hb = self.budget_cap if hb is None else min(hb, self.budget_cap)
        budget = "" if hb is None else f" {hb}"
        return (f"namespace {self.ns}\nopen DigCert\n\n"
                f"{self.cp.render_state()}\n\n"
                f"def prog : Stmt State :=\n{prog}\n\n"
                f"theorem mainQ_certified : Safe prog := by\n"
                f"  unfold prog\n  dig_vcs{budget}\n\nend {self.ns}\n")

    # ── drop pass ─────────────────────────────────────────────────────
    def run(self) -> CertifyReport:
        rep = self.report
        if self.cp is None:
            return rep
        t0 = time.monotonic()
        res: LeanResult | None = None
        rnd = 0
        while rnd < self.max_rounds:
            rnd += 1
            rep.rounds = rnd
            body = self.body()
            # large certificates get proportionally more wall time
            timeout = max(self.timeout, float(self.n_tags))
            res = check_certificate(body, self.ns, lean_bin=self.lean_bin,
                                    timeout=timeout, out_path=self.out_path)
            rep.lean_elapsed_sec += res.elapsed_sec
            rep.lean_version = res.lean_version
            rep.round_log.append({"round": rnd, "status": res.status,
                                  "failed_tags": res.failed_tags,
                                  "elapsed_sec": round(res.elapsed_sec, 2),
                                  "n_active": len(self.active)})
            if res.status == "timeout" and self._lower_budget():
                # too slow as a whole: retry with a smaller per-VC budget
                # (only completeness changes, never soundness)
                rep.round_log[-1]["budget_lowered_to"] = self.budget_cap
                rnd -= 1
                continue
            if res.certified or res.status != "failed":
                break
            progress = False
            hard = []
            for tag in set(res.failed_tags):
                parsed = self._parse_tag(tag)
                if parsed is None:
                    hard.append(tag)
                    continue
                key, which = parsed
                if which is None and key in self.active:
                    self.active.discard(key)
                    self.helpers.discard((key, "h"))
                    self.helpers.discard((key, "g"))
                    rep.dropped.append({**asdict(self.cands[key]), "round": rnd})
                    progress = True
                elif which is not None and (key, which) in self.helpers:
                    self.helpers.discard((key, which))
                    progress = True
            if hard and progress:
                # drop what we can first; an untagged failure may disappear
                # once the conjuncts it depended on are gone
                continue
            if hard and self.cp.use_frames:
                # an untagged failure can only come from a frame VC; retry
                # without frames (sound either way: Lean checks the frame)
                self.cp.use_frames = False
                rep.round_log[-1]["frames_disabled"] = True
                continue
            if hard:
                rep.reason = f"unfixable VC failure(s): {sorted(hard)}"
                break
            if not progress:
                rep.reason = "drop pass made no progress"
                break
        rep.total_elapsed_sec = time.monotonic() - t0
        if res is not None:
            rep.certificate_path = res.certificate_path
            rep.certificate_sha256 = res.certificate_sha256
        if res is not None and res.certified:
            rep.certified = [asdict(self.cands[k]) for k in sorted(self.active)]
            non_cong_missed = any(
                d.get("kind") != "Congruence" for d in rep.dropped + rep.unsupported
            )
            if not self.active:
                if non_cong_missed or not (rep.dropped or rep.unsupported):
                    rep.status = "failed"
                    rep.reason = rep.reason or "no candidate invariant survived"
                else:
                    rep.status = "certified"
                    rep.reason = "only optional congruences could not be certified"
            elif non_cong_missed:
                rep.status = "partial"
            else:
                rep.status = "certified"
        else:
            rep.certified = []
            rep.status = "failed" if res is not None and res.status == "failed" else "error"
            if res is not None and not rep.reason:
                rep.reason = (res.reason if res.status != "failed"
                              else f"round cap {self.max_rounds} reached")
        rep.loops = [{"loop": lp.idx, "head_loc": lp.head_loc,
                      "parent": lp.parent, "guard": lp.guard,
                      "frame": sorted(v for v in self.cp.vars
                                      if v not in lp.writes) if self.cp.use_frames else [],
                      "head_helpers": sorted(f"{k[0]}.{k[1]}@{w}" for k, w in self.helpers
                                             if k[0] == lp.head_loc)}
                     for lp in self.cp.loops]
        return rep

    TIMEOUT_BUDGETS = (25000, 10000, 4000)

    def _lower_budget(self) -> bool:
        cur = self.budget_cap
        for b in self.TIMEOUT_BUDGETS:
            if cur is None or b < cur:
                self.budget_cap = b
                return True
        return False

    @staticmethod
    def _parse_tag(tag: str):
        which = None
        if tag.endswith("@h") or tag.endswith("@g"):
            tag, which = tag[:-2], tag[-1]
        loc, _, k = tag.rpartition(".")
        if loc and which is not None and k.startswith("x") and k[1:].isdigit():
            return (loc, k), which                 # extra helper-only key
        if not loc or not k.isdigit():
            return None
        return (loc, int(k)), which


def certify_c_program(cfile: Path | str, dinvs, *, lean_bin: str | None = None,
                      timeout: float = 120.0, max_rounds: int = 8,
                      out_path: Path | str | None = None,
                      extra_helpers=None) -> CertifyReport:
    """Certify `dinvs` (the claims). `extra_helpers` (same shape, e.g. DIG's
    pre-`simplify` invariants) only strengthen loop-head induction."""
    return Certifier(cfile, dinvs, lean_bin=lean_bin, timeout=timeout,
                     max_rounds=max_rounds, out_path=out_path,
                     extra_helpers=extra_helpers).run()
