import Arithmetic

/-! Bounds and uniqueness only: this file does not prove density existence. -/
namespace ExternalO3DensityBounds
open ExternalO3Spec Filter

theorem failure_count_le (φ : Correction) (N : ℕ) : failureCount φ N ≤ N := by
  classical
  unfold failureCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

theorem frequency_nonneg (φ : Correction) (N : ℕ) : 0 ≤ failureFrequency φ N := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem frequency_le_one (φ : Correction) (N : ℕ) : failureFrequency φ N ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [failureFrequency, failureCount]
  · have hpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    exact (div_le_one hpos).mpr (Nat.cast_le.mpr (failure_count_le φ N))

theorem density_unique : DensityUnique := by
  intro φ d e hd he
  exact tendsto_nhds_unique hd he

theorem density_bounds (φ : Correction) (d : ℝ) (hd : HasFailureDensity φ d) :
    0 ≤ d ∧ d ≤ 1 := by
  exact ⟨ge_of_tendsto hd (Eventually.of_forall (frequency_nonneg φ)),
    le_of_tendsto hd (Eventually.of_forall (frequency_le_one φ))⟩

theorem achieved_bounded_below : BddBelow achievedDensities := by
  refine ⟨0, ?_⟩
  intro d hd
  rcases hd with ⟨φ, hφ⟩
  exact (density_bounds φ d hφ).1

end ExternalO3DensityBounds
