import Lean
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
/-
  DigCert: a tiny, Mathlib-free kernel for certifying DIG loop invariants.

  * `Stmt σ`   — shallowly embedded C statements over a per-program state σ.
  * `Eval`     — big-step semantics with five outcomes. A violated `check`
                 yields `Outcome.fail` (it does NOT get stuck), so a false
                 invariant can never be certified vacuously, including on
                 non-terminating runs: reaching a failing check takes finitely
                 many steps, hence has a finite derivation to `fail`.
  * `wp`       — computable verification-condition generator (weakest
                 precondition, loops use their annotated invariant).
  * `wp_sound` / `safe_of_wp` — proved once; certificates only discharge VCs.

  Trusted: the definitions of `Stmt`, `Eval`, `Safe` (and the Lean kernel).
  Everything else here is proved.
-/
namespace DigCert

inductive Outcome (σ : Type) where
  | normal (s : σ)
  | brk (s : σ)
  | cont (s : σ)
  | ret (s : σ)
  | fail

inductive Stmt (σ : Type) where
  | skip
  | assign (f : σ → σ)
  | seq (a b : Stmt σ)
  | ite (c : σ → Prop) (t e : Stmt σ)
  /-- `while (c) body` annotated with loop-head invariant `inv` and frame
      `fr` (the fields the loop never writes). Both annotations have no
      operational meaning; `wp` proves that `fr` is preserved. -/
  | loop (inv : σ → Prop) (fr : σ → List Int) (c : σ → Prop) (body : Stmt σ)
  | brk
  | cont
  | ret
  /-- blocking: no execution continues when `p` is false (`vassume`). -/
  | assume (p : σ → Prop)
  /-- nondeterministic update (`unknown()`, `nondet()`, uninitialised vars). -/
  | havoc (r : σ → σ → Prop)
  /-- assertion: fails explicitly when `p` is false. -/
  | check (p : σ → Prop)
  /-- turns `continue` into normal completion; `for (i;c;n) b` is
      `i; loop inv fr c (seq (catchCont b) n)`. -/
  | catchCont (a : Stmt σ)

variable {σ : Type}

def Outcome.isNormal : Outcome σ → Prop
  | .normal _ => True
  | _ => False

def Outcome.isCont : Outcome σ → Prop
  | .cont _ => True
  | _ => False

inductive Eval : Stmt σ → σ → Outcome σ → Prop
  | skip : Eval .skip s (.normal s)
  | assign : Eval (.assign f) s (.normal (f s))
  | seq_normal : Eval a s (.normal t) → Eval b t o → Eval (.seq a b) s o
  | seq_abrupt : Eval a s o → ¬ o.isNormal → Eval (.seq a b) s o
  | ite_true : c s → Eval t s o → Eval (.ite c t e) s o
  | ite_false : ¬ c s → Eval e s o → Eval (.ite c t e) s o
  | loop_exit : ¬ c s → Eval (.loop inv fr c b) s (.normal s)
  | loop_normal : c s → Eval b s (.normal t) → Eval (.loop inv fr c b) t o →
      Eval (.loop inv fr c b) s o
  | loop_cont : c s → Eval b s (.cont t) → Eval (.loop inv fr c b) t o →
      Eval (.loop inv fr c b) s o
  | loop_brk : c s → Eval b s (.brk t) → Eval (.loop inv fr c b) s (.normal t)
  | loop_ret : c s → Eval b s (.ret t) → Eval (.loop inv fr c b) s (.ret t)
  | loop_fail : c s → Eval b s .fail → Eval (.loop inv fr c b) s .fail
  | brk : Eval .brk s (.brk s)
  | cont : Eval .cont s (.cont s)
  | ret : Eval .ret s (.ret s)
  | assume : p s → Eval (.assume p) s (.normal s)
  | havoc : r s t → Eval (.havoc r) s (.normal t)
  | check_ok : p s → Eval (.check p) s (.normal s)
  | check_fail : ¬ p s → Eval (.check p) s .fail
  | catch_cont : Eval a s (.cont t) → Eval (.catchCont a) s (.normal t)
  | catch_other : Eval a s o → ¬ o.isCont → Eval (.catchCont a) s o

/-- The certified property: no execution, from any initial state, reaches a
    failing `check`. Input constraints live inside `prog` as `assume`s. -/
def Safe (prog : Stmt σ) : Prop :=
  ∀ s o, Eval prog s o → o ≠ .fail

/-- Postconditions for normal completion, `break`, and `continue`.
    `return` needs none; `fail` is never allowed. -/
structure Post (σ : Type) where
  n : σ → Prop
  b : σ → Prop
  c : σ → Prop

def Outcome.sat (Q : Post σ) : Outcome σ → Prop
  | .normal t => Q.n t
  | .brk t => Q.b t
  | .cont t => Q.c t
  | .ret _ => True
  | .fail => False

def wp : Stmt σ → Post σ → σ → Prop
  | .skip, Q => Q.n
  | .assign f, Q => fun s => Q.n (f s)
  | .seq a b, Q => wp a { Q with n := wp b Q }
  | .ite c t e, Q => fun s => (c s → wp t Q s) ∧ (¬ c s → wp e Q s)
  | .loop inv fr c body, Q => fun s =>
      -- s is the state at loop entry; t ranges over loop-head states that
      -- agree with s on the frame, so facts about unwritten fields survive.
      inv s ∧
      (∀ t, fr t = fr s → inv t → c t →
        wp body ⟨fun u => inv u ∧ fr u = fr s, Q.n,
                 fun u => inv u ∧ fr u = fr s⟩ t) ∧
      (∀ t, fr t = fr s → inv t → ¬ c t → Q.n t)
  | .brk, Q => Q.b
  | .cont, Q => Q.c
  | .ret, _ => fun _ => True
  | .assume p, Q => fun s => p s → Q.n s
  | .havoc r, Q => fun s => ∀ t, r s t → Q.n t
  | .check p, Q => fun s => p s ∧ Q.n s
  | .catchCont a, Q => wp a { Q with c := Q.n }

/-- Re-entering the loop from a head state `t` that kept the frame. -/
theorem wp_loop_reenter {inv : σ → Prop} {fr : σ → List Int} {c : σ → Prop}
    {b : Stmt σ} {Q : Post σ} {s t : σ}
    (hw : wp (.loop inv fr c b) Q s) (ht : inv t ∧ fr t = fr s) :
    wp (.loop inv fr c b) Q t := by
  obtain ⟨_, h1, h2⟩ := hw
  refine ⟨ht.1, ?_, ?_⟩
  · intro t' e; rw [ht.2] at e ⊢; exact h1 t' e
  · intro t' e; rw [ht.2] at e; exact h2 t' e

theorem wp_sound {S : Stmt σ} {s : σ} {o : Outcome σ} (h : Eval S s o) :
    ∀ Q, wp S Q s → o.sat Q := by
  induction h with
  | skip => intro Q hw; exact hw
  | assign => intro Q hw; exact hw
  | seq_normal _ _ iha ihb =>
    intro Q hw; exact ihb Q (iha _ hw)
  | seq_abrupt _ hn iha =>
    rename_i o _ _
    intro Q hw
    have := iha _ hw
    cases o <;> simp_all [Outcome.sat, Outcome.isNormal]
  | ite_true hc _ ih => intro Q hw; exact ih Q (hw.1 hc)
  | ite_false hc _ ih => intro Q hw; exact ih Q (hw.2 hc)
  | loop_exit hc => intro Q hw; exact hw.2.2 _ rfl hw.1 hc
  | loop_normal hc _ _ ihb ihl =>
    intro Q hw
    have hi := ihb _ (hw.2.1 _ rfl hw.1 hc)
    exact ihl Q (wp_loop_reenter hw hi)
  | loop_cont hc _ _ ihb ihl =>
    intro Q hw
    have hi := ihb _ (hw.2.1 _ rfl hw.1 hc)
    exact ihl Q (wp_loop_reenter hw hi)
  | loop_brk hc _ ihb =>
    intro Q hw; have h := ihb _ (hw.2.1 _ rfl hw.1 hc); exact h
  | loop_ret => intro _ _; trivial
  | loop_fail hc _ ihb =>
    intro Q hw; have h := ihb _ (hw.2.1 _ rfl hw.1 hc); exact h.elim
  | brk => intro Q hw; exact hw
  | cont => intro Q hw; exact hw
  | ret => intro _ _; trivial
  | assume hp => intro Q hw; exact hw hp
  | havoc hr => intro Q hw; exact hw _ hr
  | check_ok _ => intro Q hw; exact hw.2
  | check_fail hp => intro Q hw; exact hp hw.1
  | catch_cont _ ih => intro Q hw; exact ih _ hw
  | catch_other _ hn ih =>
    rename_i o _
    intro Q hw
    have := ih _ hw
    cases o <;> simp_all [Outcome.sat, Outcome.isCont]

/-- Havoc one `Int` field: `upd s n` is `s` with that field set to `n`.
    Used for `unknown()`/`nondet()` and uninitialised declarations. -/
def Stmt.havocInt (upd : σ → Int → σ) : Stmt σ :=
  .havoc (fun s t => ∃ n, t = upd s n)

theorem wp_havocInt (upd : σ → Int → σ) (Q : Post σ) (s : σ) :
    wp (Stmt.havocInt upd) Q s = ∀ n, Q.n (upd s n) := by
  simp only [Stmt.havocInt, wp]
  apply propext
  constructor
  · intro h n; exact h _ ⟨n, rfl⟩
  · intro h t ⟨n, hn⟩; subst hn; exact h n

/-- The top-level postcondition: after `mainQ` nothing is checked. -/
def topPost : Post σ := ⟨fun _ => True, fun _ => True, fun _ => True⟩

theorem safe_of_wp {prog : Stmt σ} (h : ∀ s, wp prog topPost s) : Safe prog := by
  intro s o he hf
  have := wp_sound he topPost (h s)
  subst hf
  exact this

/-- Labels an invariant conjunct so a failing VC can be traced back to it.
    Definitionally `p`, but irreducible so that `apply And.intro` / `intro`
    in `dig_vcs` cannot split or open a tagged conjunct (keeps attribution). -/
@[irreducible] def Tag (_name : String) (p : Prop) : Prop := p

/-! ### C integer division (truncation toward zero)

`omega` understands `/` and `%` on `Int` (Euclidean, `Int.ediv`/`Int.emod`)
but not `Int.tdiv`/`Int.tmod`. C's `/` and `%` are emitted as `cdiv`/`cmod`,
defined via `Int.tdiv`/`Int.tmod` and rewritten by `cdiv_eq`/`cmod_eq` into
Euclidean form plus a sign correction before arithmetic tactics run. -/

def cdiv (a b : Int) : Int := a.tdiv b
def cmod (a b : Int) : Int := a.tmod b

theorem cdiv_eq (a b : Int) :
    cdiv a b = a / b +
      (if 0 ≤ a ∨ a % b = 0 then 0
       else if 0 < b then 1 else if b < 0 then -1 else 0) := by
  unfold cdiv
  rw [Int.tdiv_eq_ediv]
  simp only [Int.dvd_iff_emod_eq_zero]
  congr 1
  split
  · rfl
  · rcases Int.lt_trichotomy b 0 with h | h | h
    · have h' : ¬ 0 < b := by omega
      simp [Int.sign_eq_neg_one_of_neg h, h, h']
    · subst h; simp
    · simp [Int.sign_eq_one_of_pos h, h]

theorem cmod_eq (a b : Int) : cmod a b = a - b * cdiv a b := by
  unfold cmod cdiv
  exact Int.tmod_def a b


section DivFacts
open Lean Elab Tactic Meta

/-- `a / k` or `a % k` on `Int` with `k` a numeral in `1..8`. -/
def numDivMod? (x : Expr) : Option (Expr × Nat) :=
  if x.isAppOfArity ``HDiv.hDiv 6 || x.isAppOfArity ``HMod.hMod 6 then
    if (x.getArg! 0).isConstOf ``Int then
      match (x.getArg! 5).int? with
      | some k => if 0 < k && k ≤ 8 then some (x.getArg! 4, k.toNat) else none
      | none => none
    else none
  else none

/-- Find one numeral division/modulo in the goal or hypotheses. -/
def findNumDivMod (g : MVarId) : MetaM (Option (Expr × Nat)) := g.withContext do
  let mut exprs : Array Expr := #[← instantiateMVars (← g.getType)]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then exprs := exprs.push (← instantiateMVars d.type)
  for e in exprs do
    if let some x := e.find? (fun x => (numDivMod? x).isSome) then
      return numDivMod? x
  return none

/-- For each `a / k`, `a % k` (Int, `k` a numeral in 1..8): add
    `k * (a / k) + a % k = a`, generalize quotient and remainder into fresh
    atoms, and add the remainder's possible values `r = 0 ∨ … ∨ r = k-1`.
    It only adds proved facts and abstracts terms, so it cannot make a false
    goal provable. -/
elab "dig_divfacts" : tactic => do
  for n in [0:8] do
    let some (a, k) ← findNumDivMod (← getMainGoal) | return
    let qi := mkIdent (.mkSimple s!"dq{n}")
    let ri := mkIdent (.mkSimple s!"dr{n}")
    let ei := mkIdent (.mkSimple s!"de{n}")
    let aS ← (← getMainGoal).withContext <| PrettyPrinter.delab a
    let kS := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic| have $ei:ident := Int.mul_ediv_add_emod ($aS : Int) $kS))
    evalTactic (← `(tactic| have := Int.emod_nonneg ($aS : Int) (show ($kS : Int) ≠ 0 by decide)))
    evalTactic (← `(tactic| have := Int.emod_lt_of_pos ($aS : Int) (show (0 : Int) < $kS by decide)))
    evalTactic (← `(tactic| generalize (($aS : Int) / $kS) = $qi:ident at *))
    evalTactic (← `(tactic| generalize (($aS : Int) % $kS) = $ri:ident at *))
    let mut disj ← `(term| $ri:ident = 0)
    for j in (List.range k).drop 1 do
      let jS := Syntax.mkNumLit (toString j)
      disj ← `(term| $ri:ident = $jS ∨ $disj)
    evalTactic (← `(tactic| have := (show $disj from by omega)))
    -- stop if generalization did not remove the term (avoid looping)
    if let some (a', k') ← findNumDivMod (← getMainGoal) then
      if a' == a && k' == k then return

end DivFacts

/-! ### Certificate tactics

`dig_vcs` turns `Safe prog` into its verification conditions via the proved
`safe_of_wp`, splits them into one goal per (path, invariant conjunct), and
discharges each with `trivial | omega | grind`, falling back to rewriting
C division (`cdiv_eq`/`cmod_eq`) into Euclidean form and, for numeral
divisors, abstracting quotient/remainder (`dig_divfacts`). A goal that cannot be proved
is reported as `DIG_VC_FAILED <tag>` and admitted. Admitting introduces
`sorryAx`, which the runner's `#print axioms` check rejects, so a failed VC
yields diagnostics but never a certificate. -/

/-- Heartbeat budget (in thousands) for each individual VC. -/
def goalHeartbeats : Nat := 100000

open Lean Elab Tactic Meta in
elab "dig_discharge" budget:(num)? : tactic => do
  let hb := budget.map (·.getNat) |>.getD goalHeartbeats
  let goals ← getGoals
  for g in goals do
    if ← g.isAssigned then continue
    let tgt ← instantiateMVars (← g.getType)
    let tag : String :=
      match tgt.getAppFn.constName?, tgt.getAppArgs with
      | some ``DigCert.Tag, #[.lit (.strVal s), _] => s
      | _, _ => "untagged"
    let saved ← saveState
    setGoals [g]
    -- Fresh heartbeat budget per goal. Runtime exceptions (heartbeat
    -- timeouts) are caught too, so one hard goal cannot abort the theorem.
    let attempt : TacticM Unit :=
      withTheReader Core.Context
        (fun ctx => { ctx with maxHeartbeats := hb * 1000 }) <|
      Core.withCurrHeartbeats do
        evalTactic (← `(tactic|
          ((try simp only [DigCert.Tag] at *) <;>
            first
            | trivial | omega | grind
            | ((simp only [DigCert.cmod_eq, DigCert.cdiv_eq] at *) <;>
                first | omega | grind | (dig_divfacts; grind)))))
        unless (← getGoals).isEmpty do throwError "goals remain"
    let onFail : Exception → TacticM Unit := fun _ => do
      saved.restore
      logError m!"DIG_VC_FAILED {tag}"
      g.admit
    tryCatchRuntimeEx attempt onFail
  setGoals []

/-- `dig_vcs` or `dig_vcs n`: `n` is the per-VC heartbeat budget (thousands);
    it affects only how hard each VC is tried, never soundness. -/
syntax "dig_vcs" (num)? : tactic
macro_rules
  | `(tactic| dig_vcs $[$n]?) => `(tactic| (
      apply DigCert.safe_of_wp
      intro s
      simp only [DigCert.wp_havocInt, DigCert.wp, DigCert.topPost, and_imp,
        List.cons.injEq, and_true]
      repeat' (first | apply And.intro | intro _)
      dig_discharge $[$n]?))

end DigCert
