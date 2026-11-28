import PopulationWeights

/-! Exact depth-one candidate series and source-model linear corrections.
No actual density, infimum formula or nonattainment theorem is assumed here. -/
namespace ExternalO3DepthOneSeries
open ExternalO3Spec ExternalO3PopulationWeights
open scoped BigOperators

noncomputable def ascent : ℝ := Real.log ((3 : ℝ) / 2)

noncomputable def linearCorrection (c : ℝ) : Correction :=
  fun r => ((r : ℝ) - 1) * c

noncomputable def cycleGain (R k : ℕ) : ℝ :=
  (R : ℝ) * ascent - ((k : ℝ) - 1) * Real.log 2

/-- First argument is the next-run offset; second is the exit-valuation offset. -/
noncomputable def mandatoryMass (r k : ℕ) : ℝ := by
  classical
  exact if 0 ≤ cycleGain (r + 1) (k + 2) then
    (2 : ℝ) ^ (-(k + 2 : ℤ) - (r + 1 : ℤ)) else 0

theorem ascent_pos : 0 < ascent := Real.log_pos (by norm_num)

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem ascent_eq : ascent = Real.log 3 - Real.log 2 := by
  exact Real.log_div (by norm_num) (by norm_num)

theorem linear_exit_gain (c : ℝ) (k r : ℕ) :
    exitGain (linearCorrection c) (k + 2) (r + 1) =
      cycleGain (r + 1) (k + 2) + (r : ℝ) * (c - ascent) := by
  simp only [exitGain, linearCorrection, cycleGain, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat]
  rw [ascent_eq]
  ring

theorem critical_exit_gain (k r : ℕ) :
    exitGain (linearCorrection ascent) (k + 2) (r + 1) =
      cycleGain (r + 1) (k + 2) := by
  rw [linear_exit_gain]
  simp

theorem mandatoryMass_eq_exitMass (r k : ℕ) :
    mandatoryMass r k = exitMass (linearCorrection ascent) k r := by
  classical
  simp only [mandatoryMass, exitMass, critical_exit_gain]

theorem mandatoryMass_nonneg (r k : ℕ) : 0 ≤ mandatoryMass r k := by
  classical
  unfold mandatoryMass
  split
  · exact le_of_lt (zpow_pos (by norm_num) _)
  · exact le_rfl

theorem mandatory_pair_summable :
    Summable (fun p : ℕ × ℕ => mandatoryMass p.1 p.2) := by
  have h := (selected_exit_summable (linearCorrection ascent)).prod_symm
  change Summable (fun p : ℕ × ℕ =>
    selectedWeight (linearCorrection ascent) (.inr (p.2, p.1))) at h
  simpa only [selectedWeight_inr, mandatoryMass_eq_exitMass] using h

theorem mandatory_row_summable (r : ℕ) : Summable (mandatoryMass r) := by
  exact mandatory_pair_summable.prod_factor r

noncomputable def floorThreshold (r : ℕ) : ℤ :=
  Int.floor (1 + (r : ℝ) * (ascent / Real.log 2))

theorem threshold_ge_one (r : ℕ) : 1 ≤ floorThreshold r := by
  apply Int.le_floor.mpr
  have h := mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    (le_of_lt (div_pos ascent_pos log_two_pos))
  norm_num
  linarith

theorem term_eq (r : ℕ) : depthOneTerm r =
    (2 : ℝ) ^ (-(r : ℤ)) * ((1 : ℝ) / 2 - (2 : ℝ) ^ (-floorThreshold r)) := by
  rfl

theorem threshold_power_le_half (r : ℕ) :
    (2 : ℝ) ^ (-floorThreshold r) ≤ (1 : ℝ) / 2 := by
  have h := threshold_ge_one r
  calc
    (2 : ℝ) ^ (-floorThreshold r) ≤ (2 : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = (1 : ℝ) / 2 := by norm_num

theorem depth_one_term_nonneg (r : ℕ) : 0 ≤ depthOneTerm r := by
  rw [term_eq]
  exact mul_nonneg (le_of_lt (zpow_pos (by norm_num) _))
    (sub_nonneg.mpr (threshold_power_le_half r))

theorem half_power_eq_weight (r : ℕ) :
    (2 : ℝ) ^ (-(r + 1 : ℤ)) * ((1 : ℝ) / 2) = weight (.inl r) := by
  change _ = (2 : ℝ) ^ (-(r + 2 : ℤ))
  rw [show -(r + 2 : ℤ) = -(r + 1 : ℤ) + (-1 : ℤ) by omega,
    zpow_add₀ (by norm_num)]
  norm_num

theorem depth_one_term_lt_weight (r : ℕ) : depthOneTerm (r + 1) < weight (.inl r) := by
  rw [term_eq]
  have hp := zpow_pos (by norm_num : (0 : ℝ) < 2) (-(r + 1 : ℤ))
  have hq := zpow_pos (by norm_num : (0 : ℝ) < 2) (-floorThreshold (r + 1))
  have hh := half_power_eq_weight r
  have hprod := mul_pos hp hq
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem depth_one_series_summable : DepthOneSeriesSummable := by
  exact Summable.of_nonneg_of_le (fun r => depth_one_term_nonneg (r + 1))
    (fun r => (depth_one_term_lt_weight r).le) ascending_weight_summable

theorem depth_one_series_nonneg : 0 ≤ depthOneSeries := by
  exact tsum_nonneg (fun r => depth_one_term_nonneg (r + 1))

theorem shifted_weight_summable (M : ℕ) :
    Summable (fun r : ℕ => weight (.inl (r + M))) :=
  (summable_nat_add_iff M).mpr ascending_weight_summable

theorem shifted_weight_tsum (M : ℕ) :
    (∑' r : ℕ, weight (.inl (r + M))) = (2 : ℝ) ^ (-(M + 1 : ℤ)) := by
  have he (r : ℕ) : weight (.inl (r + M)) =
      weight (.inl M) * ((1 : ℝ) / 2) ^ r := by
    simp only [weight_inl_geometric, pow_add]
    ring
  simp_rw [he]
  rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
  have h := half_power_eq_weight M
  linarith

theorem series_split (M : ℕ) :
    depthOnePartial M + (∑' r : ℕ, depthOneTerm (r + M + 1)) = depthOneSeries := by
  have hs : Summable (fun r : ℕ => depthOneTerm (r + 1)) := depth_one_series_summable
  simpa only [depthOnePartial, depthOneSeries, Nat.add_assoc] using
    Summable.sum_add_tsum_nat_add M hs

theorem shifted_term_summable (M : ℕ) :
    Summable (fun r : ℕ => depthOneTerm (r + M + 1)) := by
  have hs : Summable (fun r : ℕ => depthOneTerm (r + 1)) := depth_one_series_summable
  exact (summable_nat_add_iff M).mpr hs

theorem depth_one_tail_strict (M : ℕ) :
    depthOneSeries - depthOnePartial M < (2 : ℝ) ^ (-(M + 1 : ℤ)) := by
  have hs := series_split M
  have hlt : (∑' r : ℕ, depthOneTerm (r + M + 1)) <
      ∑' r : ℕ, weight (.inl (r + M)) := by
    exact Summable.tsum_lt_tsum (fun r => (depth_one_term_lt_weight (r + M)).le)
      (i := 0) (depth_one_term_lt_weight (0 + M))
      (shifted_term_summable M) (shifted_weight_summable M)
  rw [shifted_weight_tsum] at hlt
  linarith

theorem depth_one_tail : DepthOneTail := by
  intro M
  have hs := series_split M
  have hlo : 0 ≤ ∑' r : ℕ, depthOneTerm (r + M + 1) :=
    tsum_nonneg (fun r => depth_one_term_nonneg (r + M + 1))
  have hhi := depth_one_tail_strict M
  constructor
  · linarith
  · convert hhi.le using 1
    congr 1
    omega

theorem cycleGain_nonneg_iff (R k : ℕ) :
    0 ≤ cycleGain R k ↔ (k : ℤ) ≤ floorThreshold R := by
  change 0 ≤ (R : ℝ) * ascent - ((k : ℝ) - 1) * Real.log 2 ↔
    (k : ℤ) ≤ Int.floor (1 + (R : ℝ) * (ascent / Real.log 2))
  rw [Int.le_floor]
  simp only [Int.cast_natCast]
  have he : (R : ℝ) * (ascent / Real.log 2) = (R : ℝ) * ascent / Real.log 2 := by
    ring
  rw [he]
  constructor
  · intro h
    have hx : ((k : ℝ) - 1) * Real.log 2 ≤ (R : ℝ) * ascent := by linarith
    have hy := (le_div_iff₀ log_two_pos).mpr hx
    linarith
  · intro h
    have hy : (k : ℝ) - 1 ≤ (R : ℝ) * ascent / Real.log 2 := by linarith
    have hx := (le_div_iff₀ log_two_pos).mp hy
    linarith

noncomputable def thresholdNat (R : ℕ) : ℕ := (floorThreshold R).toNat

theorem thresholdNat_cast (R : ℕ) : (thresholdNat R : ℤ) = floorThreshold R :=
  Int.toNat_of_nonneg (by have h := threshold_ge_one R; omega)

theorem thresholdNat_pos (R : ℕ) : 0 < thresholdNat R := by
  have h := threshold_ge_one R
  have hc := thresholdNat_cast R
  omega

theorem mandatory_cutoff (r k : ℕ) :
    mandatoryMass r k = if k < thresholdNat (r + 1) - 1 then
      weight (.inr (k, r)) else 0 := by
  classical
  have he : 0 ≤ cycleGain (r + 1) (k + 2) ↔ k < thresholdNat (r + 1) - 1 := by
    rw [cycleGain_nonneg_iff]
    have hc := thresholdNat_cast (r + 1)
    omega
  simp only [mandatoryMass, he, weight]

theorem ascending_weight_partial (m : ℕ) :
    (∑ k ∈ Finset.range m, weight (.inl k)) =
      (1 : ℝ) / 2 - (2 : ℝ) ^ (-(m + 1 : ℤ)) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have he : -((m + 1 : ℕ) + 1 : ℤ) = -(m + 2 : ℤ) := by omega
    rw [he]
    have hh := half_power_eq_weight m
    change (2 : ℝ) ^ (-(m + 1 : ℤ)) * ((1 : ℝ) / 2) =
      (2 : ℝ) ^ (-(m + 2 : ℤ)) at hh
    change (1 / 2 - (2 : ℝ) ^ (-(m + 1 : ℤ))) +
      (2 : ℝ) ^ (-(m + 2 : ℤ)) = 1 / 2 - (2 : ℝ) ^ (-(m + 2 : ℤ))
    linarith

theorem mandatory_row_tsum (r : ℕ) :
    (∑' k : ℕ, mandatoryMass r k) = depthOneTerm (r + 1) := by
  classical
  let F := thresholdNat (r + 1)
  have hF : 0 < F := thresholdNat_pos (r + 1)
  have hsupport : ∀ k ∉ Finset.range (F - 1), mandatoryMass r k = 0 := by
    intro k hk
    rw [mandatory_cutoff]
    simp only [Finset.mem_range] at hk
    exact ite_eq_right hk
  rw [tsum_eq_sum hsupport]
  calc
    (∑ k ∈ Finset.range (F - 1), mandatoryMass r k) =
        ∑ k ∈ Finset.range (F - 1), weight (.inl k) * landingWeight r := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [mandatory_cutoff, ite_eq_left (Finset.mem_range.mp hk), weight_inr_mul]
    _ = (∑ k ∈ Finset.range (F - 1), weight (.inl k)) * landingWeight r := by
      rw [Finset.sum_mul]
    _ = ((1 : ℝ) / 2 - (2 : ℝ) ^ (-(F : ℤ))) * landingWeight r := by
      rw [ascending_weight_partial]
      have he : -((F - 1 : ℕ) + 1 : ℤ) = -(F : ℤ) := by omega
      rw [he]
    _ = depthOneTerm (r + 1) := by
      rw [term_eq]
      have hc : (F : ℤ) = floorThreshold (r + 1) := thresholdNat_cast (r + 1)
      rw [hc]
      simp only [landingWeight, Nat.cast_add, Nat.cast_one]
      ring

theorem mandatory_total_tsum :
    (∑' r : ℕ, ∑' k : ℕ, mandatoryMass r k) = depthOneSeries := by
  simp only [mandatory_row_tsum, depthOneSeries]

theorem mandatory_pair_tsum :
    (∑' p : ℕ × ℕ, mandatoryMass p.1 p.2) = depthOneSeries := by
  rw [mandatory_pair_summable.tsum_prod]
  exact mandatory_total_tsum

end ExternalO3DepthOneSeries
