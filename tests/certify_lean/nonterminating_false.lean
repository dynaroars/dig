/- NEGATIVE fixture: the certificate tactic must FAIL on a non-terminating
   loop with a non-inductive check (s < 2 with s incremented forever). -/
namespace Cert_nonterm_bad
open DigCert

def prog : Stmt Int :=
  .seq (.assign fun _ => 0) <|
  .loop (fun s => Tag "vtrace1.0" (s < 2)) (fun _ => []) (fun _ => True) <|
    .seq (.check fun s => Tag "vtrace1.0" (s < 2)) (.assign fun s => s + 1)

theorem mainQ_certified : Safe prog := by
  unfold prog
  dig_vcs

end Cert_nonterm_bad
