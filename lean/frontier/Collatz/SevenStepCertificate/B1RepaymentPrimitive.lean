import Collatz.SevenStepCertificate.Basic

/-! The growing B1 return, checked on a whole affine ray. -/
namespace Collatz.SevenStepCertificate

theorem b1_growth_lap (t : Nat) :
    run (.p1, 6*(128*t+17)) 7 = (.p1, 6*(729*t+98)) := by
  have h0 : next (.p1, 6*(128*t+17)) = (.p2, 1152*t+153) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h1 : next (.p2, 1152*t+153) = (.p3, 576*t+77) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h2 : next (.p3, 576*t+77) = (.p4, 864*t+116) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h3 : next (.p4, 864*t+116) = (.p5, 1296*t+174) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h4 : next (.p5, 1296*t+174) = (.p6, 1944*t+261) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  have h5 : next (.p6, 1944*t+261) = (.p0, 2916*t+392) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, T]; split <;> omega
  have h6 : next (.p0, 2916*t+392) = (.p1, 6*(729*t+98)) := by
    apply Prod.ext
    · rfl
    · simp only [next, update, U]; split <;> omega
  simp only [run, h0, h1, h2, h3, h4, h5, h6]

end Collatz.SevenStepCertificate
