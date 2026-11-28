import SpaceTopology
import SpaceArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Regularity of the literal roof observable. The circle seam is retained;
continuity is claimed only away from that seam, exactly as in the frozen goal. -/
namespace ExternalCriticalSpaceReward
open ExternalCriticalSpaceDraft ExternalCriticalSpaceArithmetic
open MeasureTheory Filter
open scoped Topology

theorem height_weight_pow (n : ℕ) : heightWeight (OnePoint.some n) = ((2 : ℝ)⁻¹)^n := by
  simp [heightWeight, zpow_neg, inv_pow]

theorem height_weight_continuous : Continuous heightWeight := by
  apply (OnePoint.continuous_iff_from_nat heightWeight).mpr
  change Tendsto (fun n : ℕ => (2 : ℝ)^(-(n : ℤ))) atTop (𝓝 0)
  simpa only [zpow_neg, zpow_natCast, inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1))

theorem height_weight_bounds (h : Height) : 0 ≤ heightWeight h ∧ heightWeight h ≤ 1 := by
  rcases h with _ | n
  · change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1
    norm_num
  · change 0 ≤ heightWeight (OnePoint.some n) ∧ heightWeight (OnePoint.some n) ≤ 1
    rw [height_weight_pow]
    exact ⟨pow_nonneg (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem phase_representative_continuousAt (x : Phase) (hx : x ≠ 0) :
    ContinuousAt phaseRepresentative x := by
  exact continuous_subtype_val.continuousAt.comp (AddCircle.continuousAt_equivIco 1 0 hx)

theorem phase_representative_measurable : Measurable phaseRepresentative := by
  apply measurable_of_countable_not_continuousAt
  apply (Set.countable_singleton (0 : Phase)).mono
  intro x hx
  by_contra hn
  exact hx (phase_representative_continuousAt x hn)

theorem local_reward_measurable : Measurable localReward := by
  apply Measurable.mul
  · exact (Real.continuous_const_rpow (a := (2 : ℝ))).measurable.comp
      (phase_representative_measurable.comp continuous_fst.measurable).neg
  · exact (height_weight_continuous.comp ((continuous_apply 0).comp continuous_snd)).measurable

theorem local_reward_bounds (w : Config) : 0 ≤ localReward w ∧ localReward w ≤ 1 := by
  have hb := height_weight_bounds (w.2 0)
  have hp := (representative_bounds w.1).1
  have hpos : 0 ≤ Real.rpow 2 (-phaseRepresentative w.1) := Real.rpow_nonneg (by norm_num) _
  have hle : Real.rpow 2 (-phaseRepresentative w.1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hp)
  exact ⟨mul_nonneg hpos hb.1, (mul_le_mul_of_nonneg_right hle hb.1).trans (by simpa using hb.2)⟩

theorem local_reward_infty (w : Config) (hw : w.2 0 = OnePoint.infty) : localReward w = 0 := by
  simp [localReward, hw, heightWeight]

theorem local_reward_continuousAt (w : Config) (hw : w.1 ≠ 0) : ContinuousAt localReward w := by
  apply ContinuousAt.mul
  · exact (Real.continuous_const_rpow (a := (2 : ℝ))).continuousAt.comp
      ((phase_representative_continuousAt w.1 hw).comp continuous_fst.continuousAt).neg
  · exact height_weight_continuous.continuousAt.comp
      ((continuous_apply 0).comp continuous_snd).continuousAt

theorem reward_roof_and_regularity : RewardRoofAndRegularity := by
  exact ⟨local_reward_measurable, local_reward_bounds, local_reward_infty, local_reward_continuousAt⟩

end ExternalCriticalSpaceReward
