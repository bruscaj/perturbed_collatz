import Collatz.SevenStepCertificate.Basic

/-! Generated whole-affine trajectory proofs and an exhaustive three-family classifier.
Regenerate with research/certification_completion/formal/generate_certificates.py.
All arithmetic and coverage proofs are checked by the Lean kernel. -/

namespace Collatz.SevenStepCertificate

def SectionPhase (p : Phase) : Prop := p = .p1 ∨ p = .p2 ∨ p = .p3 ∨ p = .p5

def weight : Phase → Nat
  | .p1 => 4 | .p2 => 7 | .p3 => 4 | .p5 => 5 | _ => 0

def rank (p : Phase) (m : Nat) : Nat := weight p * m

def Residual : Phase → Nat → Prop
  | .p1, m => m % 2 = 0
  | .p3, m => m % 4 = 3
  | .p5, m => m % 8 = 2
  | _, _ => False

def Classified (p : Phase) (m : Nat) : Prop :=
  Residual p m ∨ Captured (p,3*m) ∨
    ∃ q n k, SectionPhase q ∧ 0 < n ∧ rank q n < rank p m ∧
      run (p,3*m) k = (q,3*n)

theorem return_00 (t : Nat) :
    run (.p1, 3*(2*t+0)) 1 = (.p2, 3*(3*t+0)) := by
  have h0 : next (.p1, 3*(2*t+0)) = (.p2, 3*(3*t+0)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem classified_00 (t : Nat) (_ht : 1 ≤ t) :
    Classified .p1 (2*t+0) := by
  unfold Classified

  left
  simp only [Residual]
  omega

theorem return_01 (t : Nat) :
    run (.p1, 3*(4*t+1)) 2 = (.p3, 3*(3*t+1)) := by
  have h0 : next (.p1, 3*(4*t+1)) = (.p2, 6*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 6*t+2) = (.p3, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem classified_01 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p1 (4*t+1) := by
  unfold Classified

  by_cases hsmall : t ≤ 0
  · have hcases : t = 0 := by omega

    rcases hcases with hzero

    · subst t
      right; left
      exact ⟨4, by rfl⟩

  · right; right

    refine ⟨.p3, 3*t+1, 2, ?_, ?_, ?_, return_01 t⟩
    · simp [SectionPhase]
    · omega
    · simp only [rank, weight]; omega

theorem return_02 (t : Nat) :
    run (.p1, 3*(4*t+3)) 2 = (.p3, 3*(1*t+1)) := by
  have h0 : next (.p1, 3*(4*t+3)) = (.p2, 6*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 6*t+5) = (.p3, 3*(1*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem classified_02 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p1 (4*t+3) := by
  unfold Classified

  right; right

  refine ⟨.p3, 1*t+1, 2, ?_, ?_, ?_, return_02 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_03 (t : Nat) :
    run (.p2, 3*(2*t+0)) 1 = (.p3, 3*(3*t+0)) := by
  have h0 : next (.p2, 3*(2*t+0)) = (.p3, 3*(3*t+0)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem classified_03 (t : Nat) (_ht : 1 ≤ t) :
    Classified .p2 (2*t+0) := by
  unfold Classified

  right; right

  refine ⟨.p3, 3*t+0, 1, ?_, ?_, ?_, return_03 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_04 (t : Nat) :
    run (.p2, 3*(8*t+3)) 3 = (.p5, 3*(9*t+4)) := by
  have h0 : next (.p2, 3*(8*t+3)) = (.p3, 12*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 12*t+5) = (.p4, 18*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 18*t+8) = (.p5, 3*(9*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_04 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (8*t+3) := by
  unfold Classified

  right; right

  refine ⟨.p5, 9*t+4, 3, ?_, ?_, ?_, return_04 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_05 (t : Nat) :
    run (.p2, 3*(8*t+5)) 3 = (.p5, 3*(3*t+2)) := by
  have h0 : next (.p2, 3*(8*t+5)) = (.p3, 12*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 12*t+8) = (.p4, 6*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 6*t+4) = (.p5, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_05 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (8*t+5) := by
  unfold Classified

  right; right

  refine ⟨.p5, 3*t+2, 3, ?_, ?_, ?_, return_05 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_06 (t : Nat) :
    run (.p2, 3*(8*t+7)) 3 = (.p5, 3*(3*t+3)) := by
  have h0 : next (.p2, 3*(8*t+7)) = (.p3, 12*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 12*t+11) = (.p4, 18*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 18*t+17) = (.p5, 3*(3*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_06 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (8*t+7) := by
  unfold Classified

  right; right

  refine ⟨.p5, 3*t+3, 3, ?_, ?_, ?_, return_06 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_07 (t : Nat) :
    run (.p2, 3*(64*t+1)) 6 = (.p1, 3*(9*t+1)) := by
  have h0 : next (.p2, 3*(64*t+1)) = (.p3, 96*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+2) = (.p4, 48*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+1) = (.p5, 24*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+1) = (.p6, 12*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 12*t+1) = (.p0, 18*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 18*t+2) = (.p1, 3*(9*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_07 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+1) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+1, 6, ?_, ?_, ?_, return_07 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_08 (t : Nat) :
    run (.p2, 3*(64*t+17)) 6 = (.p1, 3*(3*t+1)) := by
  have h0 : next (.p2, 3*(64*t+17)) = (.p3, 96*t+26) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+26) = (.p4, 48*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+13) = (.p5, 24*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+7) = (.p6, 12*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 12*t+4) = (.p0, 6*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 6*t+2) = (.p1, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_08 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+17) := by
  unfold Classified

  right; right

  refine ⟨.p1, 3*t+1, 6, ?_, ?_, ?_, return_08 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_09 (t : Nat) :
    run (.p2, 3*(64*t+25)) 6 = (.p1, 3*(9*t+4)) := by
  have h0 : next (.p2, 3*(64*t+25)) = (.p3, 96*t+38) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+38) = (.p4, 48*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+19) = (.p5, 24*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+10) = (.p6, 36*t+15) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 36*t+15) = (.p0, 54*t+23) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 54*t+23) = (.p1, 3*(9*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_09 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+25) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+4, 6, ?_, ?_, ?_, return_09 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_10 (t : Nat) :
    run (.p2, 3*(64*t+33)) 6 = (.p1, 3*(3*t+2)) := by
  have h0 : next (.p2, 3*(64*t+33)) = (.p3, 96*t+50) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+50) = (.p4, 48*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+25) = (.p5, 24*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+13) = (.p6, 12*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 12*t+7) = (.p0, 18*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 18*t+11) = (.p1, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_10 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+33) := by
  unfold Classified

  right; right

  refine ⟨.p1, 3*t+2, 6, ?_, ?_, ?_, return_10 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_11 (t : Nat) :
    run (.p2, 3*(64*t+41)) 6 = (.p1, 3*(9*t+6)) := by
  have h0 : next (.p2, 3*(64*t+41)) = (.p3, 96*t+62) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+62) = (.p4, 48*t+31) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+31) = (.p5, 24*t+16) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+16) = (.p6, 36*t+24) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 36*t+24) = (.p0, 18*t+12) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 18*t+12) = (.p1, 3*(9*t+6)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_11 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+41) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+6, 6, ?_, ?_, ?_, return_11 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_12 (t : Nat) :
    run (.p2, 3*(64*t+49)) 6 = (.p1, 3*(1*t+1)) := by
  have h0 : next (.p2, 3*(64*t+49)) = (.p3, 96*t+74) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+74) = (.p4, 48*t+37) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+37) = (.p5, 24*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+19) = (.p6, 12*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 12*t+10) = (.p0, 6*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 6*t+5) = (.p1, 3*(1*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_12 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+49) := by
  unfold Classified

  right; right

  refine ⟨.p1, 1*t+1, 6, ?_, ?_, ?_, return_12 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_13 (t : Nat) :
    run (.p2, 3*(64*t+57)) 6 = (.p1, 3*(27*t+25)) := by
  have h0 : next (.p2, 3*(64*t+57)) = (.p3, 96*t+86) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 96*t+86) = (.p4, 48*t+43) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 48*t+43) = (.p5, 24*t+22) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 24*t+22) = (.p6, 36*t+33) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 36*t+33) = (.p0, 54*t+50) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 54*t+50) = (.p1, 3*(27*t+25)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_13 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (64*t+57) := by
  unfold Classified

  right; right

  refine ⟨.p1, 27*t+25, 6, ?_, ?_, ?_, return_13 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_14 (t : Nat) :
    run (.p2, 3*(128*t+9)) 7 = (.p2, 3*(9*t+1)) := by
  have h0 : next (.p2, 3*(128*t+9)) = (.p3, 192*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 192*t+14) = (.p4, 96*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 96*t+7) = (.p5, 48*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 48*t+4) = (.p6, 72*t+6) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 72*t+6) = (.p0, 36*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 36*t+3) = (.p1, 18*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 18*t+2) = (.p2, 3*(9*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem classified_14 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (128*t+9) := by
  unfold Classified

  right; right

  refine ⟨.p2, 9*t+1, 7, ?_, ?_, ?_, return_14 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_15 (t : Nat) :
    run (.p2, 3*(128*t+73)) 7 = (.p2, 3*(3*t+2)) := by
  have h0 : next (.p2, 3*(128*t+73)) = (.p3, 192*t+110) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p3, 192*t+110) = (.p4, 96*t+55) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p4, 96*t+55) = (.p5, 48*t+28) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p5, 48*t+28) = (.p6, 72*t+42) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p6, 72*t+42) = (.p0, 36*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h5 : next (.p0, 36*t+21) = (.p1, 18*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h6 : next (.p1, 18*t+11) = (.p2, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem classified_15 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p2 (128*t+73) := by
  unfold Classified

  right; right

  refine ⟨.p2, 3*t+2, 7, ?_, ?_, ?_, return_15 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_16 (t : Nat) :
    run (.p3, 3*(4*t+0)) 2 = (.p5, 3*(3*t+0)) := by
  have h0 : next (.p3, 3*(4*t+0)) = (.p4, 6*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 6*t+0) = (.p5, 3*(3*t+0)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem classified_16 (t : Nat) (_ht : 1 ≤ t) :
    Classified .p3 (4*t+0) := by
  unfold Classified

  right; right

  refine ⟨.p5, 3*t+0, 2, ?_, ?_, ?_, return_16 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_17 (t : Nat) :
    run (.p3, 3*(4*t+1)) 2 = (.p5, 3*(3*t+1)) := by
  have h0 : next (.p3, 3*(4*t+1)) = (.p4, 18*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 18*t+5) = (.p5, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem classified_17 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (4*t+1) := by
  unfold Classified

  by_cases hsmall : t ≤ 1
  · have hcases : t = 0 ∨ t = 1 := by omega

    rcases hcases with hzero | hzero

    · subst t
      right; left
      exact ⟨2, by rfl⟩

    · subst t
      right; left
      exact ⟨16, by rfl⟩

  · right; right

    refine ⟨.p5, 3*t+1, 2, ?_, ?_, ?_, return_17 t⟩
    · simp [SectionPhase]
    · omega
    · simp only [rank, weight]; omega

theorem return_18 (t : Nat) :
    run (.p3, 3*(4*t+3)) 2 = (.p5, 3*(9*t+7)) := by
  have h0 : next (.p3, 3*(4*t+3)) = (.p4, 18*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 18*t+14) = (.p5, 3*(9*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem classified_18 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (4*t+3) := by
  unfold Classified

  left
  simp only [Residual]
  omega

theorem return_19 (t : Nat) :
    run (.p3, 3*(32*t+2)) 5 = (.p1, 3*(9*t+1)) := by
  have h0 : next (.p3, 3*(32*t+2)) = (.p4, 48*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 48*t+3) = (.p5, 24*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 24*t+2) = (.p6, 36*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 36*t+3) = (.p0, 54*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 54*t+5) = (.p1, 3*(9*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_19 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (32*t+2) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+1, 5, ?_, ?_, ?_, return_19 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_20 (t : Nat) :
    run (.p3, 3*(32*t+6)) 5 = (.p1, 3*(3*t+1)) := by
  have h0 : next (.p3, 3*(32*t+6)) = (.p4, 48*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 48*t+9) = (.p5, 24*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 24*t+5) = (.p6, 12*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 12*t+3) = (.p0, 18*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 18*t+5) = (.p1, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_20 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (32*t+6) := by
  unfold Classified

  right; right

  refine ⟨.p1, 3*t+1, 5, ?_, ?_, ?_, return_20 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_21 (t : Nat) :
    run (.p3, 3*(32*t+10)) 5 = (.p1, 3*(9*t+3)) := by
  have h0 : next (.p3, 3*(32*t+10)) = (.p4, 48*t+15) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 48*t+15) = (.p5, 24*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 24*t+8) = (.p6, 36*t+12) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 36*t+12) = (.p0, 18*t+6) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 18*t+6) = (.p1, 3*(9*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_21 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (32*t+10) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+3, 5, ?_, ?_, ?_, return_21 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_22 (t : Nat) :
    run (.p3, 3*(32*t+18)) 5 = (.p1, 3*(27*t+16)) := by
  have h0 : next (.p3, 3*(32*t+18)) = (.p4, 48*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 48*t+27) = (.p5, 24*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 24*t+14) = (.p6, 36*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 36*t+21) = (.p0, 54*t+32) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 54*t+32) = (.p1, 3*(27*t+16)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_22 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (32*t+18) := by
  unfold Classified

  right; right

  refine ⟨.p1, 27*t+16, 5, ?_, ?_, ?_, return_22 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_23 (t : Nat) :
    run (.p3, 3*(32*t+22)) 5 = (.p1, 3*(9*t+7)) := by
  have h0 : next (.p3, 3*(32*t+22)) = (.p4, 48*t+33) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 48*t+33) = (.p5, 24*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 24*t+17) = (.p6, 12*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 12*t+9) = (.p0, 18*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 18*t+14) = (.p1, 3*(9*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_23 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (32*t+22) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+7, 5, ?_, ?_, ?_, return_23 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_24 (t : Nat) :
    run (.p3, 3*(32*t+30)) 5 = (.p1, 3*(3*t+3)) := by
  have h0 : next (.p3, 3*(32*t+30)) = (.p4, 48*t+45) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 48*t+45) = (.p5, 24*t+23) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 24*t+23) = (.p6, 12*t+12) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 12*t+12) = (.p0, 6*t+6) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 6*t+6) = (.p1, 3*(3*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_24 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (32*t+30) := by
  unfold Classified

  right; right

  refine ⟨.p1, 3*t+3, 5, ?_, ?_, ?_, return_24 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_25 (t : Nat) :
    run (.p3, 3*(64*t+14)) 6 = (.p2, 3*(3*t+1)) := by
  have h0 : next (.p3, 3*(64*t+14)) = (.p4, 96*t+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 96*t+21) = (.p5, 48*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 48*t+11) = (.p6, 24*t+6) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 24*t+6) = (.p0, 12*t+3) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 12*t+3) = (.p1, 6*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p1, 6*t+2) = (.p2, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_25 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (64*t+14) := by
  unfold Classified

  right; right

  refine ⟨.p2, 3*t+1, 6, ?_, ?_, ?_, return_25 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_26 (t : Nat) :
    run (.p3, 3*(64*t+26)) 6 = (.p2, 3*(9*t+4)) := by
  have h0 : next (.p3, 3*(64*t+26)) = (.p4, 96*t+39) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 96*t+39) = (.p5, 48*t+20) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 48*t+20) = (.p6, 72*t+30) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 72*t+30) = (.p0, 36*t+15) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 36*t+15) = (.p1, 18*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p1, 18*t+8) = (.p2, 3*(9*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_26 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (64*t+26) := by
  unfold Classified

  right; right

  refine ⟨.p2, 9*t+4, 6, ?_, ?_, ?_, return_26 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_27 (t : Nat) :
    run (.p3, 3*(64*t+46)) 6 = (.p2, 3*(1*t+1)) := by
  have h0 : next (.p3, 3*(64*t+46)) = (.p4, 96*t+69) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 96*t+69) = (.p5, 48*t+35) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 48*t+35) = (.p6, 24*t+18) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 24*t+18) = (.p0, 12*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 12*t+9) = (.p1, 6*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p1, 6*t+5) = (.p2, 3*(1*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_27 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (64*t+46) := by
  unfold Classified

  right; right

  refine ⟨.p2, 1*t+1, 6, ?_, ?_, ?_, return_27 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_28 (t : Nat) :
    run (.p3, 3*(64*t+58)) 6 = (.p2, 3*(3*t+3)) := by
  have h0 : next (.p3, 3*(64*t+58)) = (.p4, 96*t+87) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h1 : next (.p4, 96*t+87) = (.p5, 48*t+44) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p5, 48*t+44) = (.p6, 72*t+66) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p6, 72*t+66) = (.p0, 36*t+33) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p0, 36*t+33) = (.p1, 18*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p1, 18*t+17) = (.p2, 3*(3*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5]

theorem classified_28 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p3 (64*t+58) := by
  unfold Classified

  right; right

  refine ⟨.p2, 3*t+3, 6, ?_, ?_, ?_, return_28 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_29 (t : Nat) :
    run (.p5, 3*(8*t+0)) 3 = (.p1, 3*(9*t+0)) := by
  have h0 : next (.p5, 3*(8*t+0)) = (.p6, 36*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 36*t+0) = (.p0, 18*t+0) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 18*t+0) = (.p1, 3*(9*t+0)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_29 (t : Nat) (_ht : 1 ≤ t) :
    Classified .p5 (8*t+0) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+0, 3, ?_, ?_, ?_, return_29 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_30 (t : Nat) :
    run (.p5, 3*(8*t+2)) 3 = (.p1, 3*(27*t+7)) := by
  have h0 : next (.p5, 3*(8*t+2)) = (.p6, 36*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 36*t+9) = (.p0, 54*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 54*t+14) = (.p1, 3*(27*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_30 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (8*t+2) := by
  unfold Classified

  left
  simp only [Residual]
  omega

theorem return_31 (t : Nat) :
    run (.p5, 3*(8*t+3)) 3 = (.p1, 3*(9*t+4)) := by
  have h0 : next (.p5, 3*(8*t+3)) = (.p6, 12*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 12*t+5) = (.p0, 18*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 18*t+8) = (.p1, 3*(9*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_31 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (8*t+3) := by
  unfold Classified

  by_cases hsmall : t ≤ 0
  · have hcases : t = 0 := by omega

    rcases hcases with hzero

    · subst t
      right; left
      exact ⟨14, by rfl⟩

  · right; right

    refine ⟨.p1, 9*t+4, 3, ?_, ?_, ?_, return_31 t⟩
    · simp [SectionPhase]
    · omega
    · simp only [rank, weight]; omega

theorem return_32 (t : Nat) :
    run (.p5, 3*(8*t+5)) 3 = (.p1, 3*(3*t+2)) := by
  have h0 : next (.p5, 3*(8*t+5)) = (.p6, 12*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 12*t+8) = (.p0, 6*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 6*t+4) = (.p1, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_32 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (8*t+5) := by
  unfold Classified

  right; right

  refine ⟨.p1, 3*t+2, 3, ?_, ?_, ?_, return_32 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_33 (t : Nat) :
    run (.p5, 3*(8*t+6)) 3 = (.p1, 3*(9*t+7)) := by
  have h0 : next (.p5, 3*(8*t+6)) = (.p6, 36*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 36*t+27) = (.p0, 54*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 54*t+41) = (.p1, 3*(9*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_33 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (8*t+6) := by
  unfold Classified

  right; right

  refine ⟨.p1, 9*t+7, 3, ?_, ?_, ?_, return_33 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_34 (t : Nat) :
    run (.p5, 3*(8*t+7)) 3 = (.p1, 3*(3*t+3)) := by
  have h0 : next (.p5, 3*(8*t+7)) = (.p6, 12*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 12*t+11) = (.p0, 18*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 18*t+17) = (.p1, 3*(3*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem classified_34 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (8*t+7) := by
  unfold Classified

  right; right

  refine ⟨.p1, 3*t+3, 3, ?_, ?_, ?_, return_34 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_35 (t : Nat) :
    run (.p5, 3*(16*t+4)) 4 = (.p2, 3*(3*t+1)) := by
  have h0 : next (.p5, 3*(16*t+4)) = (.p6, 72*t+18) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 72*t+18) = (.p0, 36*t+9) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 36*t+9) = (.p1, 18*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 18*t+5) = (.p2, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3]

theorem classified_35 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (16*t+4) := by
  unfold Classified

  right; right

  refine ⟨.p2, 3*t+1, 4, ?_, ?_, ?_, return_35 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_36 (t : Nat) :
    run (.p5, 3*(16*t+9)) 4 = (.p2, 3*(3*t+2)) := by
  have h0 : next (.p5, 3*(16*t+9)) = (.p6, 24*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 24*t+14) = (.p0, 12*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 12*t+7) = (.p1, 6*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 6*t+4) = (.p2, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3]

theorem classified_36 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (16*t+9) := by
  unfold Classified

  right; right

  refine ⟨.p2, 3*t+2, 4, ?_, ?_, ?_, return_36 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_37 (t : Nat) :
    run (.p5, 3*(16*t+12)) 4 = (.p2, 3*(9*t+7)) := by
  have h0 : next (.p5, 3*(16*t+12)) = (.p6, 72*t+54) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 72*t+54) = (.p0, 36*t+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 36*t+27) = (.p1, 18*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 18*t+14) = (.p2, 3*(9*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3]

theorem classified_37 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (16*t+12) := by
  unfold Classified

  right; right

  refine ⟨.p2, 9*t+7, 4, ?_, ?_, ?_, return_37 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_38 (t : Nat) :
    run (.p5, 3*(32*t+17)) 5 = (.p3, 3*(3*t+2)) := by
  have h0 : next (.p5, 3*(32*t+17)) = (.p6, 48*t+26) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 48*t+26) = (.p0, 24*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 24*t+13) = (.p1, 12*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 12*t+7) = (.p2, 6*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p2, 6*t+4) = (.p3, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem classified_38 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (32*t+17) := by
  unfold Classified

  right; right

  refine ⟨.p3, 3*t+2, 5, ?_, ?_, ?_, return_38 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_39 (t : Nat) :
    run (.p5, 3*(128*t+1)) 7 = (.p5, 3*(9*t+1)) := by
  have h0 : next (.p5, 3*(128*t+1)) = (.p6, 192*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 192*t+2) = (.p0, 96*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 96*t+1) = (.p1, 48*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 48*t+1) = (.p2, 24*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p2, 24*t+1) = (.p3, 12*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p3, 12*t+1) = (.p4, 18*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p4, 18*t+2) = (.p5, 3*(9*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem classified_39 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (128*t+1) := by
  unfold Classified

  by_cases hsmall : t ≤ 0
  · have hcases : t = 0 := by omega

    rcases hcases with hzero

    · subst t
      right; left
      exact ⟨0, by rfl⟩

  · right; right

    refine ⟨.p5, 9*t+1, 7, ?_, ?_, ?_, return_39 t⟩
    · simp [SectionPhase]
    · omega
    · simp only [rank, weight]; omega

theorem return_40 (t : Nat) :
    run (.p5, 3*(128*t+33)) 7 = (.p5, 3*(3*t+1)) := by
  have h0 : next (.p5, 3*(128*t+33)) = (.p6, 192*t+50) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 192*t+50) = (.p0, 96*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 96*t+25) = (.p1, 48*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 48*t+13) = (.p2, 24*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p2, 24*t+7) = (.p3, 12*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p3, 12*t+4) = (.p4, 6*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p4, 6*t+2) = (.p5, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem classified_40 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (128*t+33) := by
  unfold Classified

  right; right

  refine ⟨.p5, 3*t+1, 7, ?_, ?_, ?_, return_40 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_41 (t : Nat) :
    run (.p5, 3*(128*t+65)) 7 = (.p5, 3*(3*t+2)) := by
  have h0 : next (.p5, 3*(128*t+65)) = (.p6, 192*t+98) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 192*t+98) = (.p0, 96*t+49) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 96*t+49) = (.p1, 48*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 48*t+25) = (.p2, 24*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p2, 24*t+13) = (.p3, 12*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p3, 12*t+7) = (.p4, 18*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p4, 18*t+11) = (.p5, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem classified_41 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (128*t+65) := by
  unfold Classified

  right; right

  refine ⟨.p5, 3*t+2, 7, ?_, ?_, ?_, return_41 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem return_42 (t : Nat) :
    run (.p5, 3*(128*t+97)) 7 = (.p5, 3*(1*t+1)) := by
  have h0 : next (.p5, 3*(128*t+97)) = (.p6, 192*t+146) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p6, 192*t+146) = (.p0, 96*t+73) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h2 : next (.p0, 96*t+73) = (.p1, 48*t+37) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p1, 48*t+37) = (.p2, 24*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p2, 24*t+19) = (.p3, 12*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p3, 12*t+10) = (.p4, 6*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p4, 6*t+5) = (.p5, 3*(1*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

theorem classified_42 (t : Nat) (_ht : 0 ≤ t) :
    Classified .p5 (128*t+97) := by
  unfold Classified

  right; right

  refine ⟨.p5, 1*t+1, 7, ?_, ?_, ?_, return_42 t⟩
  · simp [SectionPhase]
  · omega
  · simp only [rank, weight]; omega

theorem classify_p1 (m : Nat) (hm : 0 < m) : Classified .p1 m := by

  have hmod : m % 1 = 0 := Nat.mod_one m

  have hsplit : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hsplit with hmod | hmod
  ·

    have heq : m = 2*(m/2)+0 := by omega
    rw [heq]
    exact classified_00 (m/2) (by omega)

  ·

    have hsplit : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hsplit with hmod | hmod
    ·

      have heq : m = 4*(m/4)+1 := by omega
      rw [heq]
      exact classified_01 (m/4) (by omega)

    ·

      have heq : m = 4*(m/4)+3 := by omega
      rw [heq]
      exact classified_02 (m/4) (by omega)

theorem classify_p2 (m : Nat) (hm : 0 < m) : Classified .p2 m := by

  have hmod : m % 1 = 0 := Nat.mod_one m

  have hsplit : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hsplit with hmod | hmod
  ·

    have heq : m = 2*(m/2)+0 := by omega
    rw [heq]
    exact classified_03 (m/2) (by omega)

  ·

    have hsplit : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hsplit with hmod | hmod
    ·

      have hsplit : m % 8 = 1 ∨ m % 8 = 5 := by omega
      rcases hsplit with hmod | hmod
      ·

        have hsplit : m % 16 = 1 ∨ m % 16 = 9 := by omega
        rcases hsplit with hmod | hmod
        ·

          have hsplit : m % 32 = 1 ∨ m % 32 = 17 := by omega
          rcases hsplit with hmod | hmod
          ·

            have hsplit : m % 64 = 1 ∨ m % 64 = 33 := by omega
            rcases hsplit with hmod | hmod
            ·

              have heq : m = 64*(m/64)+1 := by omega
              rw [heq]
              exact classified_07 (m/64) (by omega)

            ·

              have heq : m = 64*(m/64)+33 := by omega
              rw [heq]
              exact classified_10 (m/64) (by omega)

          ·

            have hsplit : m % 64 = 17 ∨ m % 64 = 49 := by omega
            rcases hsplit with hmod | hmod
            ·

              have heq : m = 64*(m/64)+17 := by omega
              rw [heq]
              exact classified_08 (m/64) (by omega)

            ·

              have heq : m = 64*(m/64)+49 := by omega
              rw [heq]
              exact classified_12 (m/64) (by omega)

        ·

          have hsplit : m % 32 = 9 ∨ m % 32 = 25 := by omega
          rcases hsplit with hmod | hmod
          ·

            have hsplit : m % 64 = 9 ∨ m % 64 = 41 := by omega
            rcases hsplit with hmod | hmod
            ·

              have hsplit : m % 128 = 9 ∨ m % 128 = 73 := by omega
              rcases hsplit with hmod | hmod
              ·

                have heq : m = 128*(m/128)+9 := by omega
                rw [heq]
                exact classified_14 (m/128) (by omega)

              ·

                have heq : m = 128*(m/128)+73 := by omega
                rw [heq]
                exact classified_15 (m/128) (by omega)

            ·

              have heq : m = 64*(m/64)+41 := by omega
              rw [heq]
              exact classified_11 (m/64) (by omega)

          ·

            have hsplit : m % 64 = 25 ∨ m % 64 = 57 := by omega
            rcases hsplit with hmod | hmod
            ·

              have heq : m = 64*(m/64)+25 := by omega
              rw [heq]
              exact classified_09 (m/64) (by omega)

            ·

              have heq : m = 64*(m/64)+57 := by omega
              rw [heq]
              exact classified_13 (m/64) (by omega)

      ·

        have heq : m = 8*(m/8)+5 := by omega
        rw [heq]
        exact classified_05 (m/8) (by omega)

    ·

      have hsplit : m % 8 = 3 ∨ m % 8 = 7 := by omega
      rcases hsplit with hmod | hmod
      ·

        have heq : m = 8*(m/8)+3 := by omega
        rw [heq]
        exact classified_04 (m/8) (by omega)

      ·

        have heq : m = 8*(m/8)+7 := by omega
        rw [heq]
        exact classified_06 (m/8) (by omega)

theorem classify_p3 (m : Nat) (hm : 0 < m) : Classified .p3 m := by

  have hmod : m % 1 = 0 := Nat.mod_one m

  have hsplit : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hsplit with hmod | hmod
  ·

    have hsplit : m % 4 = 0 ∨ m % 4 = 2 := by omega
    rcases hsplit with hmod | hmod
    ·

      have heq : m = 4*(m/4)+0 := by omega
      rw [heq]
      exact classified_16 (m/4) (by omega)

    ·

      have hsplit : m % 8 = 2 ∨ m % 8 = 6 := by omega
      rcases hsplit with hmod | hmod
      ·

        have hsplit : m % 16 = 2 ∨ m % 16 = 10 := by omega
        rcases hsplit with hmod | hmod
        ·

          have hsplit : m % 32 = 2 ∨ m % 32 = 18 := by omega
          rcases hsplit with hmod | hmod
          ·

            have heq : m = 32*(m/32)+2 := by omega
            rw [heq]
            exact classified_19 (m/32) (by omega)

          ·

            have heq : m = 32*(m/32)+18 := by omega
            rw [heq]
            exact classified_22 (m/32) (by omega)

        ·

          have hsplit : m % 32 = 10 ∨ m % 32 = 26 := by omega
          rcases hsplit with hmod | hmod
          ·

            have heq : m = 32*(m/32)+10 := by omega
            rw [heq]
            exact classified_21 (m/32) (by omega)

          ·

            have hsplit : m % 64 = 26 ∨ m % 64 = 58 := by omega
            rcases hsplit with hmod | hmod
            ·

              have heq : m = 64*(m/64)+26 := by omega
              rw [heq]
              exact classified_26 (m/64) (by omega)

            ·

              have heq : m = 64*(m/64)+58 := by omega
              rw [heq]
              exact classified_28 (m/64) (by omega)

      ·

        have hsplit : m % 16 = 6 ∨ m % 16 = 14 := by omega
        rcases hsplit with hmod | hmod
        ·

          have hsplit : m % 32 = 6 ∨ m % 32 = 22 := by omega
          rcases hsplit with hmod | hmod
          ·

            have heq : m = 32*(m/32)+6 := by omega
            rw [heq]
            exact classified_20 (m/32) (by omega)

          ·

            have heq : m = 32*(m/32)+22 := by omega
            rw [heq]
            exact classified_23 (m/32) (by omega)

        ·

          have hsplit : m % 32 = 14 ∨ m % 32 = 30 := by omega
          rcases hsplit with hmod | hmod
          ·

            have hsplit : m % 64 = 14 ∨ m % 64 = 46 := by omega
            rcases hsplit with hmod | hmod
            ·

              have heq : m = 64*(m/64)+14 := by omega
              rw [heq]
              exact classified_25 (m/64) (by omega)

            ·

              have heq : m = 64*(m/64)+46 := by omega
              rw [heq]
              exact classified_27 (m/64) (by omega)

          ·

            have heq : m = 32*(m/32)+30 := by omega
            rw [heq]
            exact classified_24 (m/32) (by omega)

  ·

    have hsplit : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hsplit with hmod | hmod
    ·

      have heq : m = 4*(m/4)+1 := by omega
      rw [heq]
      exact classified_17 (m/4) (by omega)

    ·

      have heq : m = 4*(m/4)+3 := by omega
      rw [heq]
      exact classified_18 (m/4) (by omega)

theorem classify_p5 (m : Nat) (hm : 0 < m) : Classified .p5 m := by

  have hmod : m % 1 = 0 := Nat.mod_one m

  have hsplit : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hsplit with hmod | hmod
  ·

    have hsplit : m % 4 = 0 ∨ m % 4 = 2 := by omega
    rcases hsplit with hmod | hmod
    ·

      have hsplit : m % 8 = 0 ∨ m % 8 = 4 := by omega
      rcases hsplit with hmod | hmod
      ·

        have heq : m = 8*(m/8)+0 := by omega
        rw [heq]
        exact classified_29 (m/8) (by omega)

      ·

        have hsplit : m % 16 = 4 ∨ m % 16 = 12 := by omega
        rcases hsplit with hmod | hmod
        ·

          have heq : m = 16*(m/16)+4 := by omega
          rw [heq]
          exact classified_35 (m/16) (by omega)

        ·

          have heq : m = 16*(m/16)+12 := by omega
          rw [heq]
          exact classified_37 (m/16) (by omega)

    ·

      have hsplit : m % 8 = 2 ∨ m % 8 = 6 := by omega
      rcases hsplit with hmod | hmod
      ·

        have heq : m = 8*(m/8)+2 := by omega
        rw [heq]
        exact classified_30 (m/8) (by omega)

      ·

        have heq : m = 8*(m/8)+6 := by omega
        rw [heq]
        exact classified_33 (m/8) (by omega)

  ·

    have hsplit : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hsplit with hmod | hmod
    ·

      have hsplit : m % 8 = 1 ∨ m % 8 = 5 := by omega
      rcases hsplit with hmod | hmod
      ·

        have hsplit : m % 16 = 1 ∨ m % 16 = 9 := by omega
        rcases hsplit with hmod | hmod
        ·

          have hsplit : m % 32 = 1 ∨ m % 32 = 17 := by omega
          rcases hsplit with hmod | hmod
          ·

            have hsplit : m % 64 = 1 ∨ m % 64 = 33 := by omega
            rcases hsplit with hmod | hmod
            ·

              have hsplit : m % 128 = 1 ∨ m % 128 = 65 := by omega
              rcases hsplit with hmod | hmod
              ·

                have heq : m = 128*(m/128)+1 := by omega
                rw [heq]
                exact classified_39 (m/128) (by omega)

              ·

                have heq : m = 128*(m/128)+65 := by omega
                rw [heq]
                exact classified_41 (m/128) (by omega)

            ·

              have hsplit : m % 128 = 33 ∨ m % 128 = 97 := by omega
              rcases hsplit with hmod | hmod
              ·

                have heq : m = 128*(m/128)+33 := by omega
                rw [heq]
                exact classified_40 (m/128) (by omega)

              ·

                have heq : m = 128*(m/128)+97 := by omega
                rw [heq]
                exact classified_42 (m/128) (by omega)

          ·

            have heq : m = 32*(m/32)+17 := by omega
            rw [heq]
            exact classified_38 (m/32) (by omega)

        ·

          have heq : m = 16*(m/16)+9 := by omega
          rw [heq]
          exact classified_36 (m/16) (by omega)

      ·

        have heq : m = 8*(m/8)+5 := by omega
        rw [heq]
        exact classified_32 (m/8) (by omega)

    ·

      have hsplit : m % 8 = 3 ∨ m % 8 = 7 := by omega
      rcases hsplit with hmod | hmod
      ·

        have heq : m = 8*(m/8)+3 := by omega
        rw [heq]
        exact classified_31 (m/8) (by omega)

      ·

        have heq : m = 8*(m/8)+7 := by omega
        rw [heq]
        exact classified_34 (m/8) (by omega)

theorem complete_classifier (p : Phase) (m : Nat) (hp : SectionPhase p)
    (hm : 0 < m) : Classified p m := by
  rcases hp with hp | hp | hp | hp
  · subst p; exact classify_p1 m hm
  · subst p; exact classify_p2 m hm
  · subst p; exact classify_p3 m hm
  · subst p; exact classify_p5 m hm

theorem entry_01 (t : Nat) :
    run (.p0, 96*t+1) 5 = (.p5, 3*(9*t+1)) := by
  have h0 : next (.p0, 96*t+1) = (.p1, 48*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+1) = (.p2, 24*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+1) = (.p3, 12*t+1) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p3, 12*t+1) = (.p4, 18*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p4, 18*t+2) = (.p5, 3*(9*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem entry_02 (t : Nat) :
    run (.p0, 96*t+2) 1 = (.p1, 3*(48*t+1)) := by
  have h0 : next (.p0, 96*t+2) = (.p1, 3*(48*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_03 (t : Nat) :
    run (.p0, 96*t+3) 2 = (.p2, 3*(24*t+1)) := by
  have h0 : next (.p0, 96*t+3) = (.p1, 48*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+2) = (.p2, 3*(24*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_04 (t : Nat) :
    run (.p0, 96*t+4) 1 = (.p1, 3*(48*t+2)) := by
  have h0 : next (.p0, 96*t+4) = (.p1, 3*(48*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_05 (t : Nat) :
    run (.p0, 96*t+5) 1 = (.p1, 3*(16*t+1)) := by
  have h0 : next (.p0, 96*t+5) = (.p1, 3*(16*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_06 (t : Nat) :
    run (.p0, 96*t+6) 1 = (.p1, 3*(48*t+3)) := by
  have h0 : next (.p0, 96*t+6) = (.p1, 3*(48*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_07 (t : Nat) :
    run (.p0, 96*t+7) 2 = (.p2, 3*(24*t+2)) := by
  have h0 : next (.p0, 96*t+7) = (.p1, 48*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+4) = (.p2, 3*(24*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_08 (t : Nat) :
    run (.p0, 96*t+8) 1 = (.p1, 3*(48*t+4)) := by
  have h0 : next (.p0, 96*t+8) = (.p1, 3*(48*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_09 (t : Nat) :
    run (.p0, 96*t+9) 2 = (.p2, 3*(8*t+1)) := by
  have h0 : next (.p0, 96*t+9) = (.p1, 48*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+5) = (.p2, 3*(8*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_10 (t : Nat) :
    run (.p0, 96*t+10) 1 = (.p1, 3*(48*t+5)) := by
  have h0 : next (.p0, 96*t+10) = (.p1, 3*(48*t+5)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_11 (t : Nat) :
    run (.p0, 96*t+11) 1 = (.p1, 3*(16*t+2)) := by
  have h0 : next (.p0, 96*t+11) = (.p1, 3*(16*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_12 (t : Nat) :
    run (.p0, 96*t+12) 1 = (.p1, 3*(48*t+6)) := by
  have h0 : next (.p0, 96*t+12) = (.p1, 3*(48*t+6)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_13 (t : Nat) :
    run (.p0, 96*t+13) 3 = (.p3, 3*(12*t+2)) := by
  have h0 : next (.p0, 96*t+13) = (.p1, 48*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+7) = (.p2, 24*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+4) = (.p3, 3*(12*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem entry_14 (t : Nat) :
    run (.p0, 96*t+14) 1 = (.p1, 3*(48*t+7)) := by
  have h0 : next (.p0, 96*t+14) = (.p1, 3*(48*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_15 (t : Nat) :
    run (.p0, 96*t+15) 2 = (.p2, 3*(24*t+4)) := by
  have h0 : next (.p0, 96*t+15) = (.p1, 48*t+8) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+8) = (.p2, 3*(24*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_16 (t : Nat) :
    run (.p0, 96*t+16) 1 = (.p1, 3*(48*t+8)) := by
  have h0 : next (.p0, 96*t+16) = (.p1, 3*(48*t+8)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_17 (t : Nat) :
    run (.p0, 96*t+17) 1 = (.p1, 3*(16*t+3)) := by
  have h0 : next (.p0, 96*t+17) = (.p1, 3*(16*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_18 (t : Nat) :
    run (.p0, 96*t+18) 1 = (.p1, 3*(48*t+9)) := by
  have h0 : next (.p0, 96*t+18) = (.p1, 3*(48*t+9)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_19 (t : Nat) :
    run (.p0, 96*t+19) 2 = (.p2, 3*(24*t+5)) := by
  have h0 : next (.p0, 96*t+19) = (.p1, 48*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+10) = (.p2, 3*(24*t+5)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_20 (t : Nat) :
    run (.p0, 96*t+20) 1 = (.p1, 3*(48*t+10)) := by
  have h0 : next (.p0, 96*t+20) = (.p1, 3*(48*t+10)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_21 (t : Nat) :
    run (.p0, 96*t+21) 2 = (.p2, 3*(8*t+2)) := by
  have h0 : next (.p0, 96*t+21) = (.p1, 48*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+11) = (.p2, 3*(8*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_22 (t : Nat) :
    run (.p0, 96*t+22) 1 = (.p1, 3*(48*t+11)) := by
  have h0 : next (.p0, 96*t+22) = (.p1, 3*(48*t+11)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_23 (t : Nat) :
    run (.p0, 96*t+23) 1 = (.p1, 3*(16*t+4)) := by
  have h0 : next (.p0, 96*t+23) = (.p1, 3*(16*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_24 (t : Nat) :
    run (.p0, 96*t+24) 1 = (.p1, 3*(48*t+12)) := by
  have h0 : next (.p0, 96*t+24) = (.p1, 3*(48*t+12)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_25 (t : Nat) :
    run (.p0, 96*t+25) 5 = (.p5, 3*(3*t+1)) := by
  have h0 : next (.p0, 96*t+25) = (.p1, 48*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+13) = (.p2, 24*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+7) = (.p3, 12*t+4) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p3, 12*t+4) = (.p4, 6*t+2) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p4, 6*t+2) = (.p5, 3*(3*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem entry_26 (t : Nat) :
    run (.p0, 96*t+26) 1 = (.p1, 3*(48*t+13)) := by
  have h0 : next (.p0, 96*t+26) = (.p1, 3*(48*t+13)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_27 (t : Nat) :
    run (.p0, 96*t+27) 2 = (.p2, 3*(24*t+7)) := by
  have h0 : next (.p0, 96*t+27) = (.p1, 48*t+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+14) = (.p2, 3*(24*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_28 (t : Nat) :
    run (.p0, 96*t+28) 1 = (.p1, 3*(48*t+14)) := by
  have h0 : next (.p0, 96*t+28) = (.p1, 3*(48*t+14)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_29 (t : Nat) :
    run (.p0, 96*t+29) 1 = (.p1, 3*(16*t+5)) := by
  have h0 : next (.p0, 96*t+29) = (.p1, 3*(16*t+5)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_30 (t : Nat) :
    run (.p0, 96*t+30) 1 = (.p1, 3*(48*t+15)) := by
  have h0 : next (.p0, 96*t+30) = (.p1, 3*(48*t+15)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_31 (t : Nat) :
    run (.p0, 96*t+31) 2 = (.p2, 3*(24*t+8)) := by
  have h0 : next (.p0, 96*t+31) = (.p1, 48*t+16) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+16) = (.p2, 3*(24*t+8)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_32 (t : Nat) :
    run (.p0, 96*t+32) 1 = (.p1, 3*(48*t+16)) := by
  have h0 : next (.p0, 96*t+32) = (.p1, 3*(48*t+16)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_33 (t : Nat) :
    run (.p0, 96*t+33) 2 = (.p2, 3*(8*t+3)) := by
  have h0 : next (.p0, 96*t+33) = (.p1, 48*t+17) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+17) = (.p2, 3*(8*t+3)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_34 (t : Nat) :
    run (.p0, 96*t+34) 1 = (.p1, 3*(48*t+17)) := by
  have h0 : next (.p0, 96*t+34) = (.p1, 3*(48*t+17)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_35 (t : Nat) :
    run (.p0, 96*t+35) 1 = (.p1, 3*(16*t+6)) := by
  have h0 : next (.p0, 96*t+35) = (.p1, 3*(16*t+6)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_36 (t : Nat) :
    run (.p0, 96*t+36) 1 = (.p1, 3*(48*t+18)) := by
  have h0 : next (.p0, 96*t+36) = (.p1, 3*(48*t+18)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_37 (t : Nat) :
    run (.p0, 96*t+37) 3 = (.p3, 3*(12*t+5)) := by
  have h0 : next (.p0, 96*t+37) = (.p1, 48*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+19) = (.p2, 24*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+10) = (.p3, 3*(12*t+5)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem entry_38 (t : Nat) :
    run (.p0, 96*t+38) 1 = (.p1, 3*(48*t+19)) := by
  have h0 : next (.p0, 96*t+38) = (.p1, 3*(48*t+19)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_39 (t : Nat) :
    run (.p0, 96*t+39) 2 = (.p2, 3*(24*t+10)) := by
  have h0 : next (.p0, 96*t+39) = (.p1, 48*t+20) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+20) = (.p2, 3*(24*t+10)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_40 (t : Nat) :
    run (.p0, 96*t+40) 1 = (.p1, 3*(48*t+20)) := by
  have h0 : next (.p0, 96*t+40) = (.p1, 3*(48*t+20)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_41 (t : Nat) :
    run (.p0, 96*t+41) 1 = (.p1, 3*(16*t+7)) := by
  have h0 : next (.p0, 96*t+41) = (.p1, 3*(16*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_42 (t : Nat) :
    run (.p0, 96*t+42) 1 = (.p1, 3*(48*t+21)) := by
  have h0 : next (.p0, 96*t+42) = (.p1, 3*(48*t+21)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_43 (t : Nat) :
    run (.p0, 96*t+43) 2 = (.p2, 3*(24*t+11)) := by
  have h0 : next (.p0, 96*t+43) = (.p1, 48*t+22) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+22) = (.p2, 3*(24*t+11)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_44 (t : Nat) :
    run (.p0, 96*t+44) 1 = (.p1, 3*(48*t+22)) := by
  have h0 : next (.p0, 96*t+44) = (.p1, 3*(48*t+22)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_45 (t : Nat) :
    run (.p0, 96*t+45) 2 = (.p2, 3*(8*t+4)) := by
  have h0 : next (.p0, 96*t+45) = (.p1, 48*t+23) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+23) = (.p2, 3*(8*t+4)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_46 (t : Nat) :
    run (.p0, 96*t+46) 1 = (.p1, 3*(48*t+23)) := by
  have h0 : next (.p0, 96*t+46) = (.p1, 3*(48*t+23)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_47 (t : Nat) :
    run (.p0, 96*t+47) 1 = (.p1, 3*(16*t+8)) := by
  have h0 : next (.p0, 96*t+47) = (.p1, 3*(16*t+8)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_48 (t : Nat) :
    run (.p0, 96*t+48) 1 = (.p1, 3*(48*t+24)) := by
  have h0 : next (.p0, 96*t+48) = (.p1, 3*(48*t+24)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_49 (t : Nat) :
    run (.p0, 96*t+49) 5 = (.p5, 3*(3*t+2)) := by
  have h0 : next (.p0, 96*t+49) = (.p1, 48*t+25) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+25) = (.p2, 24*t+13) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+13) = (.p3, 12*t+7) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p3, 12*t+7) = (.p4, 18*t+11) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p4, 18*t+11) = (.p5, 3*(3*t+2)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem entry_50 (t : Nat) :
    run (.p0, 96*t+50) 1 = (.p1, 3*(48*t+25)) := by
  have h0 : next (.p0, 96*t+50) = (.p1, 3*(48*t+25)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_51 (t : Nat) :
    run (.p0, 96*t+51) 2 = (.p2, 3*(24*t+13)) := by
  have h0 : next (.p0, 96*t+51) = (.p1, 48*t+26) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+26) = (.p2, 3*(24*t+13)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_52 (t : Nat) :
    run (.p0, 96*t+52) 1 = (.p1, 3*(48*t+26)) := by
  have h0 : next (.p0, 96*t+52) = (.p1, 3*(48*t+26)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_53 (t : Nat) :
    run (.p0, 96*t+53) 1 = (.p1, 3*(16*t+9)) := by
  have h0 : next (.p0, 96*t+53) = (.p1, 3*(16*t+9)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_54 (t : Nat) :
    run (.p0, 96*t+54) 1 = (.p1, 3*(48*t+27)) := by
  have h0 : next (.p0, 96*t+54) = (.p1, 3*(48*t+27)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_55 (t : Nat) :
    run (.p0, 96*t+55) 2 = (.p2, 3*(24*t+14)) := by
  have h0 : next (.p0, 96*t+55) = (.p1, 48*t+28) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+28) = (.p2, 3*(24*t+14)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_56 (t : Nat) :
    run (.p0, 96*t+56) 1 = (.p1, 3*(48*t+28)) := by
  have h0 : next (.p0, 96*t+56) = (.p1, 3*(48*t+28)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_57 (t : Nat) :
    run (.p0, 96*t+57) 2 = (.p2, 3*(8*t+5)) := by
  have h0 : next (.p0, 96*t+57) = (.p1, 48*t+29) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+29) = (.p2, 3*(8*t+5)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_58 (t : Nat) :
    run (.p0, 96*t+58) 1 = (.p1, 3*(48*t+29)) := by
  have h0 : next (.p0, 96*t+58) = (.p1, 3*(48*t+29)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_59 (t : Nat) :
    run (.p0, 96*t+59) 1 = (.p1, 3*(16*t+10)) := by
  have h0 : next (.p0, 96*t+59) = (.p1, 3*(16*t+10)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_60 (t : Nat) :
    run (.p0, 96*t+60) 1 = (.p1, 3*(48*t+30)) := by
  have h0 : next (.p0, 96*t+60) = (.p1, 3*(48*t+30)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_61 (t : Nat) :
    run (.p0, 96*t+61) 3 = (.p3, 3*(12*t+8)) := by
  have h0 : next (.p0, 96*t+61) = (.p1, 48*t+31) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+31) = (.p2, 24*t+16) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+16) = (.p3, 3*(12*t+8)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem entry_62 (t : Nat) :
    run (.p0, 96*t+62) 1 = (.p1, 3*(48*t+31)) := by
  have h0 : next (.p0, 96*t+62) = (.p1, 3*(48*t+31)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_63 (t : Nat) :
    run (.p0, 96*t+63) 2 = (.p2, 3*(24*t+16)) := by
  have h0 : next (.p0, 96*t+63) = (.p1, 48*t+32) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+32) = (.p2, 3*(24*t+16)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_64 (t : Nat) :
    run (.p0, 96*t+64) 1 = (.p1, 3*(48*t+32)) := by
  have h0 : next (.p0, 96*t+64) = (.p1, 3*(48*t+32)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_65 (t : Nat) :
    run (.p0, 96*t+65) 1 = (.p1, 3*(16*t+11)) := by
  have h0 : next (.p0, 96*t+65) = (.p1, 3*(16*t+11)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_66 (t : Nat) :
    run (.p0, 96*t+66) 1 = (.p1, 3*(48*t+33)) := by
  have h0 : next (.p0, 96*t+66) = (.p1, 3*(48*t+33)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_67 (t : Nat) :
    run (.p0, 96*t+67) 2 = (.p2, 3*(24*t+17)) := by
  have h0 : next (.p0, 96*t+67) = (.p1, 48*t+34) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+34) = (.p2, 3*(24*t+17)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_68 (t : Nat) :
    run (.p0, 96*t+68) 1 = (.p1, 3*(48*t+34)) := by
  have h0 : next (.p0, 96*t+68) = (.p1, 3*(48*t+34)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_69 (t : Nat) :
    run (.p0, 96*t+69) 2 = (.p2, 3*(8*t+6)) := by
  have h0 : next (.p0, 96*t+69) = (.p1, 48*t+35) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+35) = (.p2, 3*(8*t+6)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_70 (t : Nat) :
    run (.p0, 96*t+70) 1 = (.p1, 3*(48*t+35)) := by
  have h0 : next (.p0, 96*t+70) = (.p1, 3*(48*t+35)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_71 (t : Nat) :
    run (.p0, 96*t+71) 1 = (.p1, 3*(16*t+12)) := by
  have h0 : next (.p0, 96*t+71) = (.p1, 3*(16*t+12)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_72 (t : Nat) :
    run (.p0, 96*t+72) 1 = (.p1, 3*(48*t+36)) := by
  have h0 : next (.p0, 96*t+72) = (.p1, 3*(48*t+36)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_73 (t : Nat) :
    run (.p0, 96*t+73) 5 = (.p5, 3*(1*t+1)) := by
  have h0 : next (.p0, 96*t+73) = (.p1, 48*t+37) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+37) = (.p2, 24*t+19) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+19) = (.p3, 12*t+10) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h3 : next (.p3, 12*t+10) = (.p4, 6*t+5) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h4 : next (.p4, 6*t+5) = (.p5, 3*(1*t+1)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4]

theorem entry_74 (t : Nat) :
    run (.p0, 96*t+74) 1 = (.p1, 3*(48*t+37)) := by
  have h0 : next (.p0, 96*t+74) = (.p1, 3*(48*t+37)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_75 (t : Nat) :
    run (.p0, 96*t+75) 2 = (.p2, 3*(24*t+19)) := by
  have h0 : next (.p0, 96*t+75) = (.p1, 48*t+38) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+38) = (.p2, 3*(24*t+19)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_76 (t : Nat) :
    run (.p0, 96*t+76) 1 = (.p1, 3*(48*t+38)) := by
  have h0 : next (.p0, 96*t+76) = (.p1, 3*(48*t+38)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_77 (t : Nat) :
    run (.p0, 96*t+77) 1 = (.p1, 3*(16*t+13)) := by
  have h0 : next (.p0, 96*t+77) = (.p1, 3*(16*t+13)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_78 (t : Nat) :
    run (.p0, 96*t+78) 1 = (.p1, 3*(48*t+39)) := by
  have h0 : next (.p0, 96*t+78) = (.p1, 3*(48*t+39)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_79 (t : Nat) :
    run (.p0, 96*t+79) 2 = (.p2, 3*(24*t+20)) := by
  have h0 : next (.p0, 96*t+79) = (.p1, 48*t+40) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+40) = (.p2, 3*(24*t+20)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_80 (t : Nat) :
    run (.p0, 96*t+80) 1 = (.p1, 3*(48*t+40)) := by
  have h0 : next (.p0, 96*t+80) = (.p1, 3*(48*t+40)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_81 (t : Nat) :
    run (.p0, 96*t+81) 2 = (.p2, 3*(8*t+7)) := by
  have h0 : next (.p0, 96*t+81) = (.p1, 48*t+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+41) = (.p2, 3*(8*t+7)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_82 (t : Nat) :
    run (.p0, 96*t+82) 1 = (.p1, 3*(48*t+41)) := by
  have h0 : next (.p0, 96*t+82) = (.p1, 3*(48*t+41)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_83 (t : Nat) :
    run (.p0, 96*t+83) 1 = (.p1, 3*(16*t+14)) := by
  have h0 : next (.p0, 96*t+83) = (.p1, 3*(16*t+14)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_84 (t : Nat) :
    run (.p0, 96*t+84) 1 = (.p1, 3*(48*t+42)) := by
  have h0 : next (.p0, 96*t+84) = (.p1, 3*(48*t+42)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_85 (t : Nat) :
    run (.p0, 96*t+85) 3 = (.p3, 3*(12*t+11)) := by
  have h0 : next (.p0, 96*t+85) = (.p1, 48*t+43) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+43) = (.p2, 24*t+22) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p2, 24*t+22) = (.p3, 3*(12*t+11)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2]

theorem entry_86 (t : Nat) :
    run (.p0, 96*t+86) 1 = (.p1, 3*(48*t+43)) := by
  have h0 : next (.p0, 96*t+86) = (.p1, 3*(48*t+43)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_87 (t : Nat) :
    run (.p0, 96*t+87) 2 = (.p2, 3*(24*t+22)) := by
  have h0 : next (.p0, 96*t+87) = (.p1, 48*t+44) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+44) = (.p2, 3*(24*t+22)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_88 (t : Nat) :
    run (.p0, 96*t+88) 1 = (.p1, 3*(48*t+44)) := by
  have h0 : next (.p0, 96*t+88) = (.p1, 3*(48*t+44)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_89 (t : Nat) :
    run (.p0, 96*t+89) 1 = (.p1, 3*(16*t+15)) := by
  have h0 : next (.p0, 96*t+89) = (.p1, 3*(16*t+15)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_90 (t : Nat) :
    run (.p0, 96*t+90) 1 = (.p1, 3*(48*t+45)) := by
  have h0 : next (.p0, 96*t+90) = (.p1, 3*(48*t+45)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_91 (t : Nat) :
    run (.p0, 96*t+91) 2 = (.p2, 3*(24*t+23)) := by
  have h0 : next (.p0, 96*t+91) = (.p1, 48*t+46) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+46) = (.p2, 3*(24*t+23)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_92 (t : Nat) :
    run (.p0, 96*t+92) 1 = (.p1, 3*(48*t+46)) := by
  have h0 : next (.p0, 96*t+92) = (.p1, 3*(48*t+46)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_93 (t : Nat) :
    run (.p0, 96*t+93) 2 = (.p2, 3*(8*t+8)) := by
  have h0 : next (.p0, 96*t+93) = (.p1, 48*t+47) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p1, 48*t+47) = (.p2, 3*(8*t+8)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1]

theorem entry_94 (t : Nat) :
    run (.p0, 96*t+94) 1 = (.p1, 3*(48*t+47)) := by
  have h0 : next (.p0, 96*t+94) = (.p1, 3*(48*t+47)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_95 (t : Nat) :
    run (.p0, 96*t+95) 1 = (.p1, 3*(16*t+16)) := by
  have h0 : next (.p0, 96*t+95) = (.p1, 3*(16*t+16)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_96 (t : Nat) :
    run (.p0, 96*t+96) 1 = (.p1, 3*(48*t+48)) := by
  have h0 : next (.p0, 96*t+96) = (.p1, 3*(48*t+48)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0]

theorem entry_phase_zero (z : Nat) (hz : 0 < z) :
    ∃ k, k ≤ 5 ∧ ∃ p m, SectionPhase p ∧ 0 < m ∧
      run (.p0,z) k = (p,3*m) := by
  have hbound : (z-1) % 96 < 96 := Nat.mod_lt _ (by decide)

  by_cases hpart : (z-1) % 96 < 48
  ·

    by_cases hpart : (z-1) % 96 < 24
    ·

      by_cases hpart : (z-1) % 96 < 12
      ·

        by_cases hpart : (z-1) % 96 < 6
        ·

          by_cases hpart : (z-1) % 96 < 3
          ·

            by_cases hpart : (z-1) % 96 < 1
            ·

              have h : (z-1) % 96 = 0 := by omega
              have heq : z = 96*((z-1)/96)+1 := by omega
              refine ⟨5, by decide, .p5, 9*((z-1)/96)+1, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_01 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 2
              ·

                have h : (z-1) % 96 = 1 := by omega
                have heq : z = 96*((z-1)/96)+2 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+1, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_02 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 2 := by omega
                have heq : z = 96*((z-1)/96)+3 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+1, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_03 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 4
            ·

              have h : (z-1) % 96 = 3 := by omega
              have heq : z = 96*((z-1)/96)+4 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+2, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_04 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 5
              ·

                have h : (z-1) % 96 = 4 := by omega
                have heq : z = 96*((z-1)/96)+5 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+1, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_05 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 5 := by omega
                have heq : z = 96*((z-1)/96)+6 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+3, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_06 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 9
          ·

            by_cases hpart : (z-1) % 96 < 7
            ·

              have h : (z-1) % 96 = 6 := by omega
              have heq : z = 96*((z-1)/96)+7 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+2, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_07 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 8
              ·

                have h : (z-1) % 96 = 7 := by omega
                have heq : z = 96*((z-1)/96)+8 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+4, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_08 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 8 := by omega
                have heq : z = 96*((z-1)/96)+9 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+1, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_09 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 10
            ·

              have h : (z-1) % 96 = 9 := by omega
              have heq : z = 96*((z-1)/96)+10 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+5, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_10 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 11
              ·

                have h : (z-1) % 96 = 10 := by omega
                have heq : z = 96*((z-1)/96)+11 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+2, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_11 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 11 := by omega
                have heq : z = 96*((z-1)/96)+12 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+6, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_12 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

      ·

        by_cases hpart : (z-1) % 96 < 18
        ·

          by_cases hpart : (z-1) % 96 < 15
          ·

            by_cases hpart : (z-1) % 96 < 13
            ·

              have h : (z-1) % 96 = 12 := by omega
              have heq : z = 96*((z-1)/96)+13 := by omega
              refine ⟨3, by decide, .p3, 12*((z-1)/96)+2, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_13 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 14
              ·

                have h : (z-1) % 96 = 13 := by omega
                have heq : z = 96*((z-1)/96)+14 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+7, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_14 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 14 := by omega
                have heq : z = 96*((z-1)/96)+15 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+4, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_15 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 16
            ·

              have h : (z-1) % 96 = 15 := by omega
              have heq : z = 96*((z-1)/96)+16 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+8, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_16 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 17
              ·

                have h : (z-1) % 96 = 16 := by omega
                have heq : z = 96*((z-1)/96)+17 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+3, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_17 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 17 := by omega
                have heq : z = 96*((z-1)/96)+18 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+9, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_18 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 21
          ·

            by_cases hpart : (z-1) % 96 < 19
            ·

              have h : (z-1) % 96 = 18 := by omega
              have heq : z = 96*((z-1)/96)+19 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+5, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_19 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 20
              ·

                have h : (z-1) % 96 = 19 := by omega
                have heq : z = 96*((z-1)/96)+20 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+10, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_20 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 20 := by omega
                have heq : z = 96*((z-1)/96)+21 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+2, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_21 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 22
            ·

              have h : (z-1) % 96 = 21 := by omega
              have heq : z = 96*((z-1)/96)+22 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+11, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_22 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 23
              ·

                have h : (z-1) % 96 = 22 := by omega
                have heq : z = 96*((z-1)/96)+23 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+4, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_23 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 23 := by omega
                have heq : z = 96*((z-1)/96)+24 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+12, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_24 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

    ·

      by_cases hpart : (z-1) % 96 < 36
      ·

        by_cases hpart : (z-1) % 96 < 30
        ·

          by_cases hpart : (z-1) % 96 < 27
          ·

            by_cases hpart : (z-1) % 96 < 25
            ·

              have h : (z-1) % 96 = 24 := by omega
              have heq : z = 96*((z-1)/96)+25 := by omega
              refine ⟨5, by decide, .p5, 3*((z-1)/96)+1, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_25 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 26
              ·

                have h : (z-1) % 96 = 25 := by omega
                have heq : z = 96*((z-1)/96)+26 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+13, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_26 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 26 := by omega
                have heq : z = 96*((z-1)/96)+27 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+7, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_27 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 28
            ·

              have h : (z-1) % 96 = 27 := by omega
              have heq : z = 96*((z-1)/96)+28 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+14, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_28 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 29
              ·

                have h : (z-1) % 96 = 28 := by omega
                have heq : z = 96*((z-1)/96)+29 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+5, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_29 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 29 := by omega
                have heq : z = 96*((z-1)/96)+30 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+15, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_30 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 33
          ·

            by_cases hpart : (z-1) % 96 < 31
            ·

              have h : (z-1) % 96 = 30 := by omega
              have heq : z = 96*((z-1)/96)+31 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+8, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_31 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 32
              ·

                have h : (z-1) % 96 = 31 := by omega
                have heq : z = 96*((z-1)/96)+32 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+16, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_32 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 32 := by omega
                have heq : z = 96*((z-1)/96)+33 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+3, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_33 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 34
            ·

              have h : (z-1) % 96 = 33 := by omega
              have heq : z = 96*((z-1)/96)+34 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+17, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_34 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 35
              ·

                have h : (z-1) % 96 = 34 := by omega
                have heq : z = 96*((z-1)/96)+35 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+6, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_35 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 35 := by omega
                have heq : z = 96*((z-1)/96)+36 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+18, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_36 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

      ·

        by_cases hpart : (z-1) % 96 < 42
        ·

          by_cases hpart : (z-1) % 96 < 39
          ·

            by_cases hpart : (z-1) % 96 < 37
            ·

              have h : (z-1) % 96 = 36 := by omega
              have heq : z = 96*((z-1)/96)+37 := by omega
              refine ⟨3, by decide, .p3, 12*((z-1)/96)+5, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_37 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 38
              ·

                have h : (z-1) % 96 = 37 := by omega
                have heq : z = 96*((z-1)/96)+38 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+19, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_38 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 38 := by omega
                have heq : z = 96*((z-1)/96)+39 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+10, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_39 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 40
            ·

              have h : (z-1) % 96 = 39 := by omega
              have heq : z = 96*((z-1)/96)+40 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+20, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_40 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 41
              ·

                have h : (z-1) % 96 = 40 := by omega
                have heq : z = 96*((z-1)/96)+41 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+7, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_41 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 41 := by omega
                have heq : z = 96*((z-1)/96)+42 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+21, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_42 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 45
          ·

            by_cases hpart : (z-1) % 96 < 43
            ·

              have h : (z-1) % 96 = 42 := by omega
              have heq : z = 96*((z-1)/96)+43 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+11, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_43 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 44
              ·

                have h : (z-1) % 96 = 43 := by omega
                have heq : z = 96*((z-1)/96)+44 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+22, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_44 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 44 := by omega
                have heq : z = 96*((z-1)/96)+45 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+4, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_45 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 46
            ·

              have h : (z-1) % 96 = 45 := by omega
              have heq : z = 96*((z-1)/96)+46 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+23, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_46 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 47
              ·

                have h : (z-1) % 96 = 46 := by omega
                have heq : z = 96*((z-1)/96)+47 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+8, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_47 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 47 := by omega
                have heq : z = 96*((z-1)/96)+48 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+24, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_48 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

  ·

    by_cases hpart : (z-1) % 96 < 72
    ·

      by_cases hpart : (z-1) % 96 < 60
      ·

        by_cases hpart : (z-1) % 96 < 54
        ·

          by_cases hpart : (z-1) % 96 < 51
          ·

            by_cases hpart : (z-1) % 96 < 49
            ·

              have h : (z-1) % 96 = 48 := by omega
              have heq : z = 96*((z-1)/96)+49 := by omega
              refine ⟨5, by decide, .p5, 3*((z-1)/96)+2, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_49 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 50
              ·

                have h : (z-1) % 96 = 49 := by omega
                have heq : z = 96*((z-1)/96)+50 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+25, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_50 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 50 := by omega
                have heq : z = 96*((z-1)/96)+51 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+13, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_51 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 52
            ·

              have h : (z-1) % 96 = 51 := by omega
              have heq : z = 96*((z-1)/96)+52 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+26, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_52 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 53
              ·

                have h : (z-1) % 96 = 52 := by omega
                have heq : z = 96*((z-1)/96)+53 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+9, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_53 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 53 := by omega
                have heq : z = 96*((z-1)/96)+54 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+27, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_54 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 57
          ·

            by_cases hpart : (z-1) % 96 < 55
            ·

              have h : (z-1) % 96 = 54 := by omega
              have heq : z = 96*((z-1)/96)+55 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+14, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_55 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 56
              ·

                have h : (z-1) % 96 = 55 := by omega
                have heq : z = 96*((z-1)/96)+56 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+28, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_56 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 56 := by omega
                have heq : z = 96*((z-1)/96)+57 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+5, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_57 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 58
            ·

              have h : (z-1) % 96 = 57 := by omega
              have heq : z = 96*((z-1)/96)+58 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+29, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_58 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 59
              ·

                have h : (z-1) % 96 = 58 := by omega
                have heq : z = 96*((z-1)/96)+59 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+10, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_59 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 59 := by omega
                have heq : z = 96*((z-1)/96)+60 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+30, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_60 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

      ·

        by_cases hpart : (z-1) % 96 < 66
        ·

          by_cases hpart : (z-1) % 96 < 63
          ·

            by_cases hpart : (z-1) % 96 < 61
            ·

              have h : (z-1) % 96 = 60 := by omega
              have heq : z = 96*((z-1)/96)+61 := by omega
              refine ⟨3, by decide, .p3, 12*((z-1)/96)+8, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_61 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 62
              ·

                have h : (z-1) % 96 = 61 := by omega
                have heq : z = 96*((z-1)/96)+62 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+31, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_62 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 62 := by omega
                have heq : z = 96*((z-1)/96)+63 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+16, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_63 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 64
            ·

              have h : (z-1) % 96 = 63 := by omega
              have heq : z = 96*((z-1)/96)+64 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+32, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_64 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 65
              ·

                have h : (z-1) % 96 = 64 := by omega
                have heq : z = 96*((z-1)/96)+65 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+11, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_65 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 65 := by omega
                have heq : z = 96*((z-1)/96)+66 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+33, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_66 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 69
          ·

            by_cases hpart : (z-1) % 96 < 67
            ·

              have h : (z-1) % 96 = 66 := by omega
              have heq : z = 96*((z-1)/96)+67 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+17, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_67 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 68
              ·

                have h : (z-1) % 96 = 67 := by omega
                have heq : z = 96*((z-1)/96)+68 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+34, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_68 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 68 := by omega
                have heq : z = 96*((z-1)/96)+69 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+6, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_69 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 70
            ·

              have h : (z-1) % 96 = 69 := by omega
              have heq : z = 96*((z-1)/96)+70 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+35, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_70 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 71
              ·

                have h : (z-1) % 96 = 70 := by omega
                have heq : z = 96*((z-1)/96)+71 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+12, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_71 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 71 := by omega
                have heq : z = 96*((z-1)/96)+72 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+36, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_72 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

    ·

      by_cases hpart : (z-1) % 96 < 84
      ·

        by_cases hpart : (z-1) % 96 < 78
        ·

          by_cases hpart : (z-1) % 96 < 75
          ·

            by_cases hpart : (z-1) % 96 < 73
            ·

              have h : (z-1) % 96 = 72 := by omega
              have heq : z = 96*((z-1)/96)+73 := by omega
              refine ⟨5, by decide, .p5, 1*((z-1)/96)+1, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_73 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 74
              ·

                have h : (z-1) % 96 = 73 := by omega
                have heq : z = 96*((z-1)/96)+74 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+37, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_74 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 74 := by omega
                have heq : z = 96*((z-1)/96)+75 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+19, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_75 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 76
            ·

              have h : (z-1) % 96 = 75 := by omega
              have heq : z = 96*((z-1)/96)+76 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+38, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_76 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 77
              ·

                have h : (z-1) % 96 = 76 := by omega
                have heq : z = 96*((z-1)/96)+77 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+13, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_77 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 77 := by omega
                have heq : z = 96*((z-1)/96)+78 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+39, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_78 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 81
          ·

            by_cases hpart : (z-1) % 96 < 79
            ·

              have h : (z-1) % 96 = 78 := by omega
              have heq : z = 96*((z-1)/96)+79 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+20, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_79 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 80
              ·

                have h : (z-1) % 96 = 79 := by omega
                have heq : z = 96*((z-1)/96)+80 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+40, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_80 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 80 := by omega
                have heq : z = 96*((z-1)/96)+81 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+7, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_81 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 82
            ·

              have h : (z-1) % 96 = 81 := by omega
              have heq : z = 96*((z-1)/96)+82 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+41, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_82 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 83
              ·

                have h : (z-1) % 96 = 82 := by omega
                have heq : z = 96*((z-1)/96)+83 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+14, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_83 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 83 := by omega
                have heq : z = 96*((z-1)/96)+84 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+42, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_84 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

      ·

        by_cases hpart : (z-1) % 96 < 90
        ·

          by_cases hpart : (z-1) % 96 < 87
          ·

            by_cases hpart : (z-1) % 96 < 85
            ·

              have h : (z-1) % 96 = 84 := by omega
              have heq : z = 96*((z-1)/96)+85 := by omega
              refine ⟨3, by decide, .p3, 12*((z-1)/96)+11, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_85 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 86
              ·

                have h : (z-1) % 96 = 85 := by omega
                have heq : z = 96*((z-1)/96)+86 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+43, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_86 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 86 := by omega
                have heq : z = 96*((z-1)/96)+87 := by omega
                refine ⟨2, by decide, .p2, 24*((z-1)/96)+22, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_87 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 88
            ·

              have h : (z-1) % 96 = 87 := by omega
              have heq : z = 96*((z-1)/96)+88 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+44, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_88 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 89
              ·

                have h : (z-1) % 96 = 88 := by omega
                have heq : z = 96*((z-1)/96)+89 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+15, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_89 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 89 := by omega
                have heq : z = 96*((z-1)/96)+90 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+45, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_90 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

        ·

          by_cases hpart : (z-1) % 96 < 93
          ·

            by_cases hpart : (z-1) % 96 < 91
            ·

              have h : (z-1) % 96 = 90 := by omega
              have heq : z = 96*((z-1)/96)+91 := by omega
              refine ⟨2, by decide, .p2, 24*((z-1)/96)+23, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_91 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 92
              ·

                have h : (z-1) % 96 = 91 := by omega
                have heq : z = 96*((z-1)/96)+92 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+46, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_92 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 92 := by omega
                have heq : z = 96*((z-1)/96)+93 := by omega
                refine ⟨2, by decide, .p2, 8*((z-1)/96)+8, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_93 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

          ·

            by_cases hpart : (z-1) % 96 < 94
            ·

              have h : (z-1) % 96 = 93 := by omega
              have heq : z = 96*((z-1)/96)+94 := by omega
              refine ⟨1, by decide, .p1, 48*((z-1)/96)+47, ?_, ?_, ?_⟩
              · simp [SectionPhase]
              · omega
              · have cert := entry_94 ((z-1)/96)
                rw [← heq] at cert
                exact cert

            ·

              by_cases hpart : (z-1) % 96 < 95
              ·

                have h : (z-1) % 96 = 94 := by omega
                have heq : z = 96*((z-1)/96)+95 := by omega
                refine ⟨1, by decide, .p1, 16*((z-1)/96)+16, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_95 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

              ·

                have h : (z-1) % 96 = 95 := by omega
                have heq : z = 96*((z-1)/96)+96 := by omega
                refine ⟨1, by decide, .p1, 48*((z-1)/96)+48, ?_, ?_, ?_⟩
                · simp [SectionPhase]
                · omega
                · have cert := entry_96 ((z-1)/96)
                  rw [← heq] at cert
                  exact cert

end Collatz.SevenStepCertificate
