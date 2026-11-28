import RateProductMoments

/-! Finite second-moment lower mass bound; no correction integrability is involved. -/
namespace ExternalO3RateCantelli
open ExternalO3RateDraft ExternalO3GeneralDraft ExternalO3GeneralWeights
open ExternalO3RateMoments ExternalO3RateProductMoments
open scoped BigOperators

theorem log_ratio_gap : 4 * Real.log 2 < 7 * Real.log ((3 : ℝ) / 2) := by
  have hh : Real.log ((2 : ℝ) ^ 11) < Real.log ((3 : ℝ) ^ 7) :=
    Real.log_lt_log (by positivity) (by norm_num)
  simp only [Real.log_pow, Nat.cast_ofNat] at hh
  rw [Real.log_div (by norm_num) (by norm_num)]
  linarith

theorem cycle_gain_length (h : Depth) (r : History h) :
    cycleGain h r = Real.log ((3 : ℝ) / 2) * lengthSum (h.val + 1) r -
      ((h.val + 1 : ℕ) : ℝ) * Real.log 2 := by
  simp only [cycleGain, cyclicLength, Fin.ofNat_val_eq_self, Nat.cast_add, Nat.cast_one,
    Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, lengthSum]
  ring

theorem good_of_center (h : Depth) (r : History h)
    (hc : -(((h.val + 1 : ℕ) : ℝ) / 4) ≤ centeredSum (h.val + 1) r) :
    0 < cycleGain h r := by
  have hn : (0 : ℝ) < ((h.val + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  have hg := mul_pos (sub_pos.mpr log_ratio_gap) hn
  have hs := mul_nonneg ha.le
    (sub_nonneg.mpr hc)
  have he := centeredSum_eq (h.val + 1) r
  rw [cycle_gain_length]
  nlinarith

theorem quadratic_hasSum (n : ℕ) :
    HasSum (fun r : Fin n → ℕ => productWeight n r * (8 - centeredSum n r) ^ 2)
      (64 + 2 * (n : ℝ)) := by
  convert ((productWeight_hasSum n).mul_left 64 |>.sub
    ((centered_first_hasSum n).mul_left 16)).add (centered_second_hasSum n) using 1
  · funext r
    ring
  · ring

theorem positive_cycle_mass_lower_bound : PositiveCycleMassLowerBound := by
  classical
  intro h
  let n := h.val + 1
  let D : ℝ := (n : ℝ) / 4 + 8
  let good : History h → ℝ := fun r => if 0 < cycleGain h r then productWeight n r else 0
  let q : History h → ℝ := fun r => productWeight n r * (8 - centeredSum n r) ^ 2 * (D ^ 2)⁻¹
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hD : 0 < D := by dsimp [D]; linarith
  have hD2 : 0 < D ^ 2 := sq_pos_of_pos hD
  have hgood0 (r : History h) : 0 ≤ good r := by
    dsimp [good]
    split
    · exact (productWeight_positive n r).le
    · exact le_rfl
  have hgoodle (r : History h) : good r ≤ productWeight n r := by
    dsimp [good]
    split
    · exact le_rfl
    · exact (productWeight_positive _ _).le
  have hgoods : Summable good :=
    Summable.of_nonneg_of_le hgood0 hgoodle (productWeight_summable n)
  have hq := (quadratic_hasSum n).mul_right ((D ^ 2)⁻¹)
  have hpoint (r : History h) : productWeight n r ≤ good r + q r := by
    have hq0 : 0 ≤ q r := by
      exact mul_nonneg (mul_nonneg (productWeight_positive n r).le (sq_nonneg _))
        (inv_nonneg.mpr (sq_nonneg _))
    by_cases hg : 0 < cycleGain h r
    · simp only [good, hg, ite_true]
      linarith
    · have hc : centeredSum n r < -((n : ℝ) / 4) := by
        by_contra hne
        exact hg (good_of_center h r (by simpa only [n] using le_of_not_gt hne))
      have hz : D ≤ 8 - centeredSum n r := by dsimp [D]; linarith
      have hsq : D ^ 2 ≤ (8 - centeredSum n r) ^ 2 := by nlinarith
      have hratio : 1 ≤ (8 - centeredSum n r) ^ 2 * (D ^ 2)⁻¹ := by
        exact (one_le_div hD2).mpr hsq
      have hw := mul_le_mul_of_nonneg_left hratio (productWeight_positive n r).le
      simpa [good, hg, q, mul_assoc] using hw
  have htotal := Summable.tsum_le_tsum hpoint (productWeight_summable n) (hgoods.add hq.summable)
  have hqsum : (∑' r : History h, q r) = (32 : ℝ) / ((n : ℝ) + 32) := by
    calc
      _ = (64 + 2 * (n : ℝ)) * (D ^ 2)⁻¹ := hq.tsum_eq
      _ = (32 : ℝ) / ((n : ℝ) + 32) := by
        dsimp [D]
        field_simp; ring
  have hmass : (∑' r : History h, good r) = positiveCycleMass h := by
    unfold positiveCycleMass
    apply tsum_congr
    intro r
    by_cases hg : 0 < cycleGain h r <;>
      simp [good, hg, history_weight_product, n]
  rw [Summable.tsum_add hgoods hq.summable, productWeight_tsum n, hqsum, hmass] at htotal
  have hu : (n : ℝ) / ((n : ℝ) + 32) + 32 / ((n : ℝ) + 32) = 1 := by
    field_simp
  have hl : (n : ℝ) / ((n : ℝ) + 32) ≤ positiveCycleMass h := by linarith
  norm_num [n, Nat.cast_add, Nat.cast_one, add_assoc] at hl ⊢
  exact hl

end ExternalO3RateCantelli
