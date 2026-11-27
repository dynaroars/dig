/- Hand-written certificate body for benchmark/c/nla/ps2.c (M1 fixture).
   Concatenated after DigCert.lean by the runner. -/
namespace Cert_ps2
open DigCert

structure State where
  k : Int
  x : Int
  y : Int
  c : Int

def inv1 : State → Prop := fun s =>
  Tag "vtrace1.0" (s.y * s.y + s.y - 2 * s.x = 0) ∧
  Tag "vtrace1.1" (s.c - s.y = 0) ∧
  Tag "vtrace1.2" (s.c - s.k ≤ 0) ∧
  Tag "vtrace1.3" (-s.c ≤ 0)

def prog : Stmt State :=
  .seq (.assume fun s => s.k ≥ 0) <|
  .seq (.assume fun s => s.k ≤ 30) <|
  .seq (.assign fun s => { s with y := 0 }) <|
  .seq (.assign fun s => { s with x := 0 }) <|
  .seq (.assign fun s => { s with c := 0 }) <|
  .seq (.loop inv1 (fun _ => []) (fun _ => True) <|
          .seq (.check fun s => Tag "vtrace1.0" (s.y * s.y + s.y - 2 * s.x = 0)) <|
          .seq (.check fun s => Tag "vtrace1.1" (s.c - s.y = 0)) <|
          .seq (.check fun s => Tag "vtrace1.2" (s.c - s.k ≤ 0)) <|
          .seq (.check fun s => Tag "vtrace1.3" (-s.c ≤ 0)) <|
          .seq (.ite (fun s => ¬ (s.c < s.k)) .brk .skip) <|
          .seq (.assign fun s => { s with c := s.c + 1 }) <|
          .seq (.assign fun s => { s with y := s.y + 1 }) <|
                (.assign fun s => { s with x := s.y + s.x })) <|
  .ret

theorem mainQ_certified : Safe prog := by
  unfold prog inv1
  dig_vcs

end Cert_ps2
