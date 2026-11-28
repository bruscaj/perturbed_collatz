import WordClamp

/-! Finite clamp fiber cardinality and exact crossing-cost reward bound. -/
namespace ExternalBridgePressureWordClampCount
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureWordArithmetic ExternalBridgePressureWordReward
open ExternalBridgePressureWordPopulation ExternalBridgePressureWordPartitions
open ExternalBridgePressureWordPhaseUp ExternalBridgePressureWordClamp
open scoped BigOperators

theorem clamp_bits_card (x y : ℝ) (n : ℕ) :
    Nat.card (CapDifference x y n → Bool) = 2^Dcount x y n := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  rfl

theorem clamp_fiber_bits_injective (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y)
    (v : Word n) : Function.Injective
      (fun w : {w : AuxWords y n // clampWord x n w.val = v} => clampBits x y n w.val.val) := by
  intro a b hab
  apply Subtype.ext
  apply clamp_code_injective x y n hxy
  apply Prod.ext
  · exact a.property.trans b.property.symm
  · exact hab

theorem clamp_fiber_count : ClampFiberCount := by
  intro x y n hxy _
  refine ⟨clamp_bits_card x y n, fun v => ?_⟩
  have := aux_words_finite y n hxy.2.1
  refine ⟨inferInstance, ?_⟩
  calc
    Nat.card {w : AuxWords y n // clampWord x n w.val = v} ≤
        Nat.card (CapDifference x y n → Bool) :=
      Nat.card_le_card_of_injective _ (clamp_fiber_bits_injective x y n hxy v)
    _ = _ := clamp_bits_card x y n

theorem clamp_term_bound (x y : ℝ) (n : ℕ) (hxy : OrderedPhases x y) (hn : 1 ≤ n)
    (w : Word n) (hw : AuxWord y n w) (t : Fin n) :
    auxTerm y n w t ≤ auxTerm x n (clampWord x n w) t +
      (if auxCap x t.val < auxCap y t.val then (1 : ℝ) else 0) := by
  classical
  have hc := (clamp_word_transport x y n hxy hn w hw).2.2
  have hy := (normalized_reward_law y n w hxy.2.1 hw).2.1 t
  have hx := (normalized_reward_law x n (clampWord x n w) hxy.1 hc).2.1 t
  by_cases hd : auxCap x t.val < auxCap y t.val
  · simp only [hd,ite_true]
    linarith [hy.2.2,hx.2.1]
  · simp only [hd,ite_false,add_zero]
    have hcap := hw.2.2.2 t
    have hm := cap_mono x y hxy.2.2 t.val
    have he : wordPrefix n (clampWord x n w) t.castSucc = wordPrefix n w t.castSucc := by
      rw [clamp_prefix x y n hxy w hw]
      unfold clampProfile
      apply min_eq_left
      simp only [Fin.val_castSucc]
      omega
    rw [hy.1,hx.1,he]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    linarith [hxy.2.2]

theorem cap_difference_indicator_sum (x y : ℝ) (n : ℕ) :
    (∑ t : Fin n, if auxCap x t.val < auxCap y t.val then (1 : ℝ) else 0) =
      (Dcount x y n : ℝ) := by
  classical
  calc
    _ = ∑' _t : CapDifference x y n, (1 : ℝ) := by
      convert (tsum_predicate_finite (fun t : Fin n => auxCap x t.val < auxCap y t.val) (fun _ => (1 : ℝ))).symm using 1
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : auxCap x t.val < auxCap y t.val <;> simp only [h,ite_true,ite_false]
    _ = _ := by simp [Dcount,tsum_fintype,Nat.card_eq_fintype_card]

theorem clamp_reward_bound : ClampRewardBound := by
  intro x y n hxy hn w hw
  calc
    auxReward y n w ≤ ∑ t : Fin n, (auxTerm x n (clampWord x n w) t +
        if auxCap x t.val < auxCap y t.val then (1 : ℝ) else 0) :=
      Finset.sum_le_sum (fun t _ => clamp_term_bound x y n hxy hn w hw t)
    _ = auxReward x n (clampWord x n w) + (Dcount x y n : ℝ) := by
      rw [Finset.sum_add_distrib,cap_difference_indicator_sum]
      rfl

end ExternalBridgePressureWordClampCount
