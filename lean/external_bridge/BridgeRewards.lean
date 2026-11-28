import BridgeExpectedTypes
import RungTransfer

/-! Exact reward identities for every finite word, not only admissible bridges. -/
namespace ExternalFiniteBridgeRewards
open ExternalFiniteBridgeDraft
open scoped BigOperators

theorem lowerLast_prefix_open (r : ℕ) (w : Word r) (t : Fin r) :
    wordPrefix r (lowerLast r w) t.castSucc = wordPrefix r w t.castSucc := by
  unfold wordPrefix
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < t.val
  · have hn : i.val + 1 ≠ r := by have ht := t.isLt; omega
    simp only [Fin.val_castSucc, hi, ite_true, lowerLast, hn, ite_false]
  · simp only [Fin.val_castSucc, hi, ite_false]

theorem raiseLast_prefix_open (r : ℕ) (w : Word r) (t : Fin r) :
    wordPrefix r (raiseLast r w) t.castSucc = wordPrefix r w t.castSucc := by
  unfold wordPrefix
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < t.val
  · have hn : i.val + 1 ≠ r := by have ht := t.isLt; omega
    simp only [Fin.val_castSucc, hi, ite_true, raiseLast, hn, ite_false]
  · simp only [Fin.val_castSucc, hi, ite_false]

theorem reward_endpoint_invariant : RewardEndpointInvariant := by
  intro r w
  constructor
  · unfold reward
    apply Finset.sum_congr rfl
    intro t _
    rw [lowerLast_prefix_open]
  · unfold reward
    apply Finset.sum_congr rfl
    intro t _
    rw [raiseLast_prefix_open]

theorem two_rpow_slope : Real.rpow 2 slope = 3 := by
  simp only [Real.rpow_eq_pow]
  have hl : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : Real.log (2 : ℝ) * slope = Real.log 3 := by
    unfold slope
    field_simp
  erw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), he,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem two_rpow_nat_slope (t : ℕ) :
    Real.rpow 2 ((t : ℝ) * slope) = (3 : ℝ) ^ t := by
  simp only [Real.rpow_eq_pow]
  erw [mul_comm (t : ℝ) slope, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_eq_pow (2 : ℝ) slope, two_rpow_slope, Real.rpow_natCast]

theorem reward_term_real_power (K : ℤ) (t : ℕ) :
    Real.rpow 2 ((K : ℝ) - (t : ℝ) * slope) = (2 : ℝ) ^ K / (3 : ℝ) ^ t := by
  simp only [Real.rpow_eq_pow]
  erw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast,
    ← Real.rpow_eq_pow (2 : ℝ) ((t : ℝ) * slope), two_rpow_nat_slope]

theorem reward_real_power : RewardRealPower := by
  intro r w
  unfold powerReward reward
  apply Finset.sum_congr rfl
  intro t _
  exact reward_term_real_power _ _

theorem depth_term_real_power (θ : ℝ) (K : ℤ) (t : ℕ) :
    Real.rpow 2 ((floorAt θ t : ℝ) - (t : ℝ) * θ) *
      (2 : ℝ) ^ (-(floorAt θ t - K)) =
        Real.rpow 2 ((K : ℝ) - (t : ℝ) * θ) := by
  erw [← Real.rpow_intCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

theorem source_depth_reward : SourceDepthReward := by
  intro r w
  rw [← (reward_endpoint_invariant r w).1, ← reward_real_power r (lowerLast r w)]
  unfold powerReward depthReward sourceBridgeDepth wordDepth
  apply Finset.sum_congr rfl
  intro t _
  exact (depth_term_real_power slope _ t.val).symm

theorem reference_at_rungs : ReferenceAtRungs := by
  intro r hr
  unfold literalReference phaseZeroReference
  apply Finset.sum_congr rfl
  intro t _
  rw [show literalCap slope r t.val = floorAt slope t.val from
    ExternalRungTransfer.rung_cap slope r t.val hr t.isLt]

end ExternalFiniteBridgeRewards
