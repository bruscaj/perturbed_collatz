import Collatz.SevenStepCertificate.Basic

/-! Whole-family S06/S08 merger. Capture is transferred only from a smaller-rank launch. -/
namespace Collatz.SevenStepCertificate

def oldRank (p : Phase) (m : Nat) : Nat := if p = .p6 then 2*m else m
def rho (p : Phase) (m : Nat) : Nat := 2 * oldRank p m + if p = .p6 then 1 else 0

theorem strict_refinement (p q : Phase) (m n : Nat)
    (h : oldRank p m < oldRank q n) : rho p m < rho q n := by
  unfold rho
  split <;> split <;> omega

theorem merger_rank_gap (m : Nat) : rho .p6 m = rho .p5 (2*m) + 1 := by
  simp only [rho, oldRank]
  simp

/-- Every m = 3 mod 4 phase-six launch coalesces with the doubled phase-five launch. -/
theorem phase_six_merger (q : Nat) :
    run (.p6, 3*(4*q+3)) 2 = run (.p5, 3*(2*(4*q+3))) 3 := by
  have a : next (.p6, 3*(4*q+3)) = (.p0,18*q+14) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have b : next (.p0,18*q+14) = (.p1,27*q+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have c : next (.p5, 3*(2*(4*q+3))) = (.p6,36*q+27) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have d : next (.p6,36*q+27) = (.p0,54*q+41) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have e : next (.p0,54*q+41) = (.p1,27*q+21) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, a, b, c, d, e]

/-- The merger is also an equality in the original signed physical recurrence. -/
theorem phase_six_signed_merger (q : Nat) :
    physicalRun (.p6, (12*q+9 : Nat)) 2 =
      physicalRun (.p5, (24*q+17 : Nat)) 3 := by
  have h := congrArg decode (phase_six_merger q)
  rw [run_faithful (.p6, 3*(4*q+3)) (by omega),
      run_faithful (.p5, 3*(2*(4*q+3))) (by omega)] at h
  have a : decode (Phase.p6,3*(4*q+3)) = (Phase.p6,((12*q+9 : Nat) : Int)) := by
    apply Prod.ext
    · rfl
    · simp only [decode,physical,height]; omega
  have b : decode (Phase.p5,3*(2*(4*q+3))) = (Phase.p5,((24*q+17 : Nat) : Int)) := by
    apply Prod.ext
    · rfl
    · simp only [decode,physical,height]; omega
  simpa only [a,b] using h

theorem phase_six_capture_reduction (q : Nat)
    (h : Captured (.p5,3*(2*(4*q+3)))) : Captured (.p6,3*(4*q+3)) :=
  captured_of_coalescence _ _ 2 3 (phase_six_merger q) h

/-- Both complete historical families satisfy the merger guard. -/
theorem s06_merger (t : Nat) :
    run (.p6,3*(16*t+7)) 2 = run (.p5,3*(32*t+14)) 3 := by
  have h := phase_six_merger (4*t+1)
  have a : 4*(4*t+1)+3 = 16*t+7 := by omega
  have b : 2*(16*t+7) = 32*t+14 := by omega
  simpa only [a,b] using h

theorem s08_merger (t : Nat) :
    run (.p6,3*(64*t+15)) 2 = run (.p5,3*(128*t+30)) 3 := by
  have h := phase_six_merger (16*t+3)
  have a : 4*(16*t+3)+3 = 64*t+15 := by omega
  have b : 2*(64*t+15) = 128*t+30 := by omega
  simpa only [a,b] using h

end Collatz.SevenStepCertificate
