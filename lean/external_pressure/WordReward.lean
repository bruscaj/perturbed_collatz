import WordArithmetic

/-! Exact finite normalized-reward identities and bounds. -/
namespace ExternalBridgePressureWordReward
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open scoped BigOperators

theorem two_rpow_nat_slope (t : ℕ) :
    Real.rpow 2 ((t : ℝ) * slope) = (3 : ℝ) ^ t := by
  have hl : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hs : Real.rpow 2 slope = 3 := by
    have he : Real.log (2 : ℝ) * slope = Real.log 3 := by
      unfold slope
      field_simp
    simp only [Real.rpow_eq_pow]
    erw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), he,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  simp only [Real.rpow_eq_pow] at hs ⊢
  erw [mul_comm (t : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hs,
    Real.rpow_natCast]

theorem aux_term_real_power (x : ℝ) (n : ℕ) (w : Word n) (t : Fin n) :
    auxTerm x n w t =
      Real.rpow 2 ((wordPrefix n w t.castSucc : ℝ)-x-(t.val : ℝ)*slope) := by
  unfold auxTerm
  simp only [Real.rpow_eq_pow]
  erw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), ← Real.rpow_eq_pow (2 : ℝ) ((t.val : ℝ)*slope), two_rpow_nat_slope,
    Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem normalized_reward_law : NormalizedRewardLaw := by
  intro x n w _ hw
  have ht (t : Fin n) : auxTerm x n w t =
      Real.rpow 2 ((wordPrefix n w t.castSucc : ℝ)-x-(t.val : ℝ)*slope) ∧
      0 < auxTerm x n w t ∧ auxTerm x n w t ≤ 1 := by
    refine ⟨aux_term_real_power x n w t, ?_, ?_⟩
    · rw [aux_term_real_power]
      exact Real.rpow_pos_of_pos (by norm_num) _
    · rw [aux_term_real_power]
      have hc := hw.2.2.2 t
      have hf := Int.floor_le (x+(t.val : ℝ)*slope)
      have hcast : (wordPrefix n w t.castSucc : ℝ) ≤ (auxCap x t.val : ℝ) :=
        by exact_mod_cast hc
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      unfold auxCap at hcast
      linarith
  refine ⟨?_, ht, ?_, ?_⟩
  · simp only [auxReward, auxTerm, reward, Finset.mul_sum]
  · exact Finset.sum_nonneg (fun t _ => le_of_lt (ht t).2.1)
  · calc
      auxReward x n w ≤ ∑ _t : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => (ht t).2.2)
      _ = (n : ℝ) := by simp

end ExternalBridgePressureWordReward
