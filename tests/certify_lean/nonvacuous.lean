/- Semantic sanity checks for DigCert (M1). Concatenated after DigCert.lean.
   These are PROVED facts showing `Safe` is not vacuous: programs whose
   checks can be violated — including inside a non-terminating loop — are
   provably not Safe. -/
namespace Cert_nonvacuous
open DigCert

/-- A failing check at top level is unsafe. -/
theorem check_false_unsafe : ¬ Safe (Stmt.check (fun _ : Int => False)) := by
  intro h
  exact h 0 .fail (Eval.check_fail (by simp)) rfl

/-- `while (1) { check(False); }` never terminates normally, yet is unsafe:
    the failing check is reached in finitely many steps. -/
theorem nonterminating_unsafe :
    ¬ Safe (Stmt.loop (fun _ : Int => True) (fun _ => []) (fun _ => True)
              (Stmt.check (fun _ => False))) := by
  intro h
  exact h 0 .fail (Eval.loop_fail trivial (Eval.check_fail (by simp))) rfl

/-- `s := 0; while (1) { check(s < 2); s := s + 1 }` fails on the 3rd
    iteration; still a finite derivation. -/
def counter : Stmt Int :=
  .seq (.assign fun _ => 0) <|
  .loop (fun _ => True) (fun _ => []) (fun _ => True) <|
    .seq (.check fun s => s < 2) (.assign fun s => s + 1)

theorem counter_unsafe : ¬ Safe counter := by
  intro h
  apply h 0 .fail _ rfl
  unfold counter
  refine Eval.seq_normal Eval.assign ?_
  refine Eval.loop_normal trivial (Eval.seq_normal (Eval.check_ok (by decide)) Eval.assign) ?_
  refine Eval.loop_normal trivial (Eval.seq_normal (Eval.check_ok (by decide)) Eval.assign) ?_
  exact Eval.loop_fail trivial (Eval.seq_abrupt (Eval.check_fail (by decide)) (by simp [Outcome.isNormal]))

end Cert_nonvacuous

#print axioms Cert_nonvacuous.counter_unsafe
