import DepthOneFormula
import LogRatioIrrational
import PositiveCeilReturns

/-! Nonattainment for every source-model correction; no boundedness restriction. -/
namespace ExternalO3DepthOneNonattainment
open ExternalO3Spec ExternalO3PopulationWeights ExternalO3DepthOneSeries
open ExternalO3DepthOneLower ExternalO3DepthOneFormula
open ExternalO3LogRatio ExternalO3PositiveCeilReturns
open scoped BigOperators

noncomputable def initialSurplus (φ : Correction) : ℝ := φ 2 - φ 1 - ascent

theorem initialSurplus_pos (φ : Correction)
    (hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0) : 0 < initialSurplus φ := by
  have h := hgood 0
  norm_num [ascendingGain] at h
  change 0 < φ 2 - φ 1 - Real.log ((3 : ℝ) / 2)
  linarith

/-- The strict margin at the first ascending edge persists at every later level. -/
theorem persistent_surplus (φ : Correction) (r : ℕ)
    (hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0) :
    initialSurplus φ ≤ φ (r + 2) - φ 1 - ((r + 1 : ℕ) : ℝ) * ascent := by
  induction r with
  | zero => simp [initialSurplus]
  | succ r ih =>
    have h := hgood (r + 1)
    unfold ascendingGain at h
    rw [show r + 1 + 2 - 1 = r + 2 by omega] at h
    change initialSurplus φ ≤ φ (r + 1 + 2) - φ 1 - ((r + 1 + 1 : ℕ) : ℝ) * ascent
    dsimp [ascent] at *
    push_cast at *
    nlinarith

theorem persistent_surplus_at_level (φ : Correction) (R : ℕ) (hR : 2 ≤ R)
    (hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0) :
    initialSurplus φ ≤ φ R - φ 1 - ((R : ℝ) - 1) * ascent := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hR
  have he : (((2 + r : ℕ) : ℝ) - 1) = ((r + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Nat.add_comm 2 r]
  exact persistent_surplus φ r hgood

theorem exit_gain_surplus (φ : Correction) (R K : ℕ) :
    exitGain φ K R = cycleGain R K + (φ R - φ 1 - ((R : ℝ) - 1) * ascent) := by
  unfold exitGain cycleGain
  rw [ascent_eq]
  ring

/-- One nonmandatory failing exit contributes strictly positive extra mass. -/
theorem strict_of_extra_exit (φ : Correction) (r k : ℕ)
    (hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0)
    (hcycle : cycleGain (r + 1) (k + 2) < 0)
    (hexit : 0 ≤ exitGain φ (k + 2) (r + 1)) :
    depthOneSeries < symbolicFailureDensity φ := by
  classical
  have hpoint : mandatoryMass r k < exitMass φ k r := by
    have hm : mandatoryMass r k = 0 := by
      simp only [mandatoryMass, ite_eq_right (not_le_of_gt hcycle)]
    have he : exitMass φ k r = (2 : ℝ) ^ (-(k + 2 : ℤ) - (r + 1 : ℤ)) := by
      simp only [exitMass, ite_eq_left hexit]
    rw [hm, he]
    exact zpow_pos (by norm_num) _
  have ht : (∑' p : ℕ × ℕ, mandatoryMass p.1 p.2) <
      ∑' p : ℕ × ℕ, exitMass φ p.2 p.1 := by
    exact Summable.tsum_lt_tsum
      (fun p => mandatoryMass_le_exitMass φ p.1 p.2 (fun i _ => hgood i))
      (i := (r, k)) hpoint mandatory_pair_summable (exit_pair_summable φ).prod_symm
  rw [mandatory_pair_tsum] at ht
  have heq : (∑' p : ℕ × ℕ, exitMass φ p.2 p.1) =
      ∑' k : ℕ, ∑' r : ℕ, exitMass φ k r := by
    have hprod : (∑' p : ℕ × ℕ, exitMass φ p.2 p.1) =
        ∑' r : ℕ, ∑' k : ℕ, exitMass φ k r := by
      exact (exit_pair_summable φ).prod_symm.tsum_prod
    exact hprod.trans (exit_totals_comm φ)
  rw [heq] at ht
  have hA : 0 ≤ ∑' i : ℕ, ascendingMass φ i := tsum_nonneg (ascendingMass_nonneg φ)
  unfold symbolicFailureDensity
  linarith

/-- A positive ceiling return smaller than the fixed surplus creates an extra failed exit. -/
theorem strict_of_ceiling_return (φ : Correction) (R : ℕ) (hR : 2 ≤ R)
    (hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0)
    (hgap : 0 < (Int.ceil ((R : ℝ) * (ascent / Real.log 2)) : ℝ) -
      (R : ℝ) * (ascent / Real.log 2))
    (hsmall : (Int.ceil ((R : ℝ) * (ascent / Real.log 2)) : ℝ) -
      (R : ℝ) * (ascent / Real.log 2) < initialSurplus φ / Real.log 2) :
    depthOneSeries < symbolicFailureDensity φ := by
  let x : ℝ := (R : ℝ) * (ascent / Real.log 2)
  let gap : ℝ := (Int.ceil x : ℝ) - x
  let K : ℕ := Nat.ceil x + 1
  have hx : 0 < x := mul_pos (Nat.cast_pos.mpr (by omega)) (div_pos ascent_pos log_two_pos)
  have hK : 2 ≤ K := by
    have hceil : 0 < Nat.ceil x := Nat.ceil_pos.mpr hx
    dsimp [K]
    omega
  have hcast : (K : ℝ) - 1 = (Int.ceil x : ℝ) := by
    dsimp [K]
    push_cast
    rw [natCast_ceil_eq_intCast_ceil hx.le]
    ring
  have hmul : (R : ℝ) * ascent = x * Real.log 2 := by
    dsimp [x]
    rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt log_two_pos)]
  have hcyc : cycleGain R K = -(Real.log 2) * gap := by
    unfold cycleGain
    rw [hcast]
    dsimp [gap]
    nlinarith
  have hg : 0 < gap := hgap
  have hsm : gap < initialSurplus φ / Real.log 2 := hsmall
  have hneg : cycleGain R K < 0 := by
    rw [hcyc]
    nlinarith [mul_pos log_two_pos hg]
  have hbound : gap * Real.log 2 < initialSurplus φ :=
    (lt_div_iff₀ log_two_pos).mp hsm
  have hs := persistent_surplus_at_level φ R hR hgood
  have hexit : 0 ≤ exitGain φ K R := by
    rw [exit_gain_surplus, hcyc]
    nlinarith
  have hRsub : R - 1 + 1 = R := by omega
  have hKsub : K - 2 + 2 = K := by omega
  apply strict_of_extra_exit φ (R - 1) (K - 2) hgood
  · simpa only [hRsub, hKsub] using hneg
  · simpa only [hRsub, hKsub] using hexit

theorem all_good_strict (φ : Correction)
    (hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0) :
    depthOneSeries < symbolicFailureDensity φ := by
  have hε : 0 < initialSurplus φ / Real.log 2 :=
    div_pos (initialSurplus_pos φ hgood) log_two_pos
  obtain ⟨R, hR, hgap, hsmall⟩ := exists_positive_ceil_gap
    (ascent / Real.log 2) ascent_ratio_irrational (initialSurplus φ / Real.log 2) hε
  exact strict_of_ceiling_return φ R hR hgood hgap hsmall

/-- Strictness for every unrestricted correction in the literal source-density problem. -/
theorem depth_one_not_attained : DepthOneNotAttained := by
  intro φ d hd
  have hformula : failureInfimum = depthOneSeries := depth_one_formula
  change failureInfimum < d
  rw [hformula, achieved_eq_symbolic φ d hd]
  by_cases hbad : ∃ i : ℕ, 0 ≤ ascendingGain φ (i + 2)
  · exact depth_one_strict_of_bad_ascending φ hbad
  · apply all_good_strict φ
    intro i
    exact lt_of_not_ge (fun hi => hbad ⟨i, hi⟩)

end ExternalO3DepthOneNonattainment
