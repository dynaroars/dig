/- Hand-written certificate body for benchmark/c/nla/cohendiv.c (M1 fixture,
   nested loops). Concatenated after DigCert.lean by the runner. -/
namespace Cert_cohendiv
open DigCert

structure State where
  x : Int
  y : Int
  q : Int
  r : Int
  a : Int
  b : Int

def inv1 : State → Prop := fun s =>
  Tag "vtrace1.0" (s.q * s.y + s.r - s.x = 0) ∧
  Tag "vtrace1.1" (s.a * s.y - s.b = 0) ∧
  Tag "vtrace1.2" (-s.r ≤ 0) ∧
  Tag "vtrace1.3" (1 - s.y ≤ 0)

def inv2 : State → Prop := fun s =>
  Tag "vtrace2.0" (s.q * s.y + s.r - s.x = 0) ∧
  Tag "vtrace2.1" (s.a * s.y - s.b = 0) ∧
  Tag "vtrace2.2" (s.b - s.r ≤ 0) ∧
  Tag "vtrace2.3" (1 - s.y ≤ 0)

def prog : Stmt State :=
  .seq (.assume fun s => s.x ≥ 1 ∧ s.y ≥ 1) <|
  .seq (.assign fun s => { s with q := 0 }) <|
  .seq (.assign fun s => { s with r := s.x }) <|
  .seq (.assign fun s => { s with a := 0 }) <|
  .seq (.assign fun s => { s with b := 0 }) <|
  .seq (.loop inv1 (fun _ => []) (fun _ => True) <|
          .seq (.check fun s => Tag "vtrace1.0" (s.q * s.y + s.r - s.x = 0)) <|
          .seq (.check fun s => Tag "vtrace1.1" (s.a * s.y - s.b = 0)) <|
          .seq (.check fun s => Tag "vtrace1.2" (-s.r ≤ 0)) <|
          .seq (.check fun s => Tag "vtrace1.3" (1 - s.y ≤ 0)) <|
          .seq (.ite (fun s => ¬ (s.r ≥ s.y)) .brk .skip) <|
          .seq (.assign fun s => { s with a := 1 }) <|
          .seq (.assign fun s => { s with b := s.y }) <|
          .seq (.loop inv2 (fun _ => []) (fun _ => True) <|
                  .seq (.check fun s => Tag "vtrace2.0" (s.q * s.y + s.r - s.x = 0)) <|
                  .seq (.check fun s => Tag "vtrace2.1" (s.a * s.y - s.b = 0)) <|
                  .seq (.check fun s => Tag "vtrace2.2" (s.b - s.r ≤ 0)) <|
                  .seq (.check fun s => Tag "vtrace2.3" (1 - s.y ≤ 0)) <|
                  .seq (.ite (fun s => ¬ (s.r ≥ 2 * s.b)) .brk .skip) <|
                  .seq (.assign fun s => { s with a := 2 * s.a }) <|
                        (.assign fun s => { s with b := 2 * s.b })) <|
          .seq (.assign fun s => { s with r := s.r - s.b }) <|
                (.assign fun s => { s with q := s.q + s.a })) <|
  .ret

theorem mainQ_certified : Safe prog := by
  unfold prog inv1 inv2
  dig_vcs

end Cert_cohendiv
