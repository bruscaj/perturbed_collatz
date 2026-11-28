import ExcursionMoment
import Mathlib.Analysis.PSeries

/-! The exact 12/7 lower-tail premise contradicts the proved first moment:
its n-weighted tail dominates c*n^(-5/7), a divergent p-series. -/
namespace ExternalCriticalPolynomialContradiction
open ExternalCriticalSpaceDraft ExternalCriticalExcursionMoment MeasureTheory
open scoped Topology
noncomputable section

theorem weighted_rpow_identity (n : ℕ) (hn : 0 < n) :
    Real.rpow (n : ℝ) (-((5 : ℝ)/7)) =
      (n : ℝ)*Real.rpow (n : ℝ) (-((12 : ℝ)/7)) := by
  simp only [Real.rpow_eq_pow]
  rw [show -((5 : ℝ)/7) = 1 + -((12 : ℝ)/7) by norm_num,
    Real.rpow_add (Nat.cast_pos.mpr hn),Real.rpow_one]

theorem polynomial_excursion_contradiction : PolynomialExcursionContradiction := by
  intro mu hmu H L hL c hc htail
  have hm := excursion_first_moment mu hmu H L hL
  have hs : Summable (fun n : ℕ => c*Real.rpow (n : ℝ) (-((5 : ℝ)/7))) := by
    apply (summable_nat_add_iff (L+2)).mp
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _
      ((summable_nat_add_iff (L+2)).mpr hm)
    intro n
    have hn : 0 < n+(L+2) := by omega
    have ht := mul_le_mul_of_nonneg_left (htail (n+(L+2)) (by omega))
      (Nat.cast_nonneg (n+(L+2)) : (0 : ℝ) ≤ ((n+(L+2) : ℕ) : ℝ))
    calc
      c*Real.rpow ((n+(L+2) : ℕ) : ℝ) (-((5 : ℝ)/7)) =
          ((n+(L+2) : ℕ) : ℝ) *
            (c*Real.rpow ((n+(L+2) : ℕ) : ℝ) (-((12 : ℝ)/7))) := by
        rw [weighted_rpow_identity _ hn]
        ring
      _ ≤ _ := ht
  have hp : Summable (fun n : ℕ => Real.rpow (n : ℝ) (-((5 : ℝ)/7))) :=
    (summable_mul_left_iff hc.ne').mp hs
  have he := Real.summable_nat_rpow.mp (by simpa only [Real.rpow_eq_pow] using hp)
  norm_num at he

end
end ExternalCriticalPolynomialContradiction
