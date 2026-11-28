import PopulationWeights
import DepthOneSeries

/-! Lower bound for the literal, unrestricted depth-one correction class. -/
namespace ExternalO3DepthOneLower
open ExternalO3Spec ExternalO3PopulationWeights ExternalO3DepthOneSeries
open scoped BigOperators

/-- Good ascending edges force a lower bound on every correction increment. -/
theorem potential_increment_lower (φ : Correction) (r : ℕ)
    (hgood : ∀ i : ℕ, i < r → ascendingGain φ (i + 2) < 0) :
    (r : ℝ) * Real.log ((3 : ℝ) / 2) ≤ φ (r + 1) - φ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev := ih (fun i hi => hgood i (by omega))
    have hstep := hgood r (by omega)
    unfold ascendingGain at hstep
    rw [show r + 2 - 1 = r + 1 by omega] at hstep
    push_cast
    nlinarith

/-- Telescoping needs no nonzero-cycle hypothesis: weakly nonnegative cycles force failure. -/
theorem exit_gain_ge_cycle (φ : Correction) (r k : ℕ)
    (hgood : ∀ i : ℕ, i < r → ascendingGain φ (i + 2) < 0) :
    ((r + 1 : ℕ) : ℝ) * Real.log ((3 : ℝ) / 2) -
      (((k + 2 : ℕ) : ℝ) - 1) * Real.log 2 ≤ exitGain φ (k + 2) (r + 1) := by
  have hp := potential_increment_lower φ r hgood
  have hlog : Real.log ((3 : ℝ) / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  unfold exitGain
  push_cast
  nlinarith

theorem ascendingMass_nonneg (φ : Correction) (i : ℕ) : 0 ≤ ascendingMass φ i := by
  exact selectedWeight_nonneg φ (.inl i)

theorem exitMass_nonneg (φ : Correction) (k r : ℕ) : 0 ≤ exitMass φ k r := by
  exact selectedWeight_nonneg φ (.inr (k, r))

theorem exit_pair_summable (φ : Correction) :
    Summable (fun p : ℕ × ℕ => exitMass φ p.1 p.2) := by
  convert selected_exit_summable φ using 1
  funext p
  rcases p with ⟨k, r⟩
  rfl

theorem landing_exit_summable (φ : Correction) (r : ℕ) :
    Summable (fun k : ℕ => exitMass φ k r) := by
  exact (exit_pair_summable φ).prod_symm.prod_factor r

theorem landing_totals_summable (φ : Correction) :
    Summable (fun r : ℕ => ∑' k : ℕ, exitMass φ k r) := by
  exact (exit_pair_summable φ).prod_symm.prod

theorem exit_totals_comm (φ : Correction) :
    (∑' r : ℕ, ∑' k : ℕ, exitMass φ k r) =
      ∑' k : ℕ, ∑' r : ℕ, exitMass φ k r := by
  exact (exit_pair_summable φ).tsum_comm

/-- Every mandatory exit is a failure if the ascending route to its landing level is good. -/
theorem mandatoryMass_le_exitMass (φ : Correction) (r k : ℕ)
    (hgood : ∀ i : ℕ, i < r → ascendingGain φ (i + 2) < 0) :
    mandatoryMass r k ≤ exitMass φ k r := by
  classical
  have hbound : cycleGain (r + 1) (k + 2) ≤ exitGain φ (k + 2) (r + 1) :=
    exit_gain_ge_cycle φ r k hgood
  unfold mandatoryMass
  split_ifs with hcycle
  · have hbad := hcycle.trans hbound
    simp only [exitMass, ite_eq_left hbad]
    exact le_rfl
  · exact exitMass_nonneg φ k r

theorem depthOneTerm_le_exit_row (φ : Correction) (r : ℕ)
    (hgood : ∀ i : ℕ, i < r → ascendingGain φ (i + 2) < 0) :
    depthOneTerm (r + 1) ≤ ∑' k : ℕ, exitMass φ k r := by
  rw [← mandatory_row_tsum r]
  exact Summable.tsum_le_tsum (fun k => mandatoryMass_le_exitMass φ r k hgood)
    (mandatory_row_summable r) (landing_exit_summable φ r)

/-- Below the first bad ascending edge, each mandatory row is charged to disjoint exit mass. -/
theorem partial_le_exit_total (φ : Correction) (M : ℕ)
    (hgood : ∀ i : ℕ, i + 1 < M → ascendingGain φ (i + 2) < 0) :
    depthOnePartial M ≤ ∑' k : ℕ, ∑' r : ℕ, exitMass φ k r := by
  calc
    depthOnePartial M ≤ ∑ r ∈ Finset.range M, ∑' k : ℕ, exitMass φ k r := by
      apply Finset.sum_le_sum
      intro r hr
      apply depthOneTerm_le_exit_row φ r
      intro i hi
      exact hgood i (by have := Finset.mem_range.mp hr; omega)
    _ ≤ ∑' r : ℕ, ∑' k : ℕ, exitMass φ k r := by
      exact Summable.sum_le_tsum (Finset.range M)
        (fun r _ => tsum_nonneg (exitMass_nonneg φ · r)) (landing_totals_summable φ)
    _ = ∑' k : ℕ, ∑' r : ℕ, exitMass φ k r := exit_totals_comm φ

/-- Universal lower bound over every real correction, with no boundedness restriction. -/
theorem depth_one_lower (φ : Correction) : depthOneSeries ≤ symbolicFailureDensity φ := by
  classical
  have hAnonneg : 0 ≤ ∑' i : ℕ, ascendingMass φ i := tsum_nonneg (ascendingMass_nonneg φ)
  by_cases hbad : ∃ i : ℕ, 0 ≤ ascendingGain φ (i + 2)
  · let j := Nat.find hbad
    have hj : 0 ≤ ascendingGain φ (j + 2) := Nat.find_spec hbad
    have hgood : ∀ i : ℕ, i + 1 < j + 1 → ascendingGain φ (i + 2) < 0 := by
      intro i hi
      exact lt_of_not_ge (Nat.find_min hbad (by omega))
    have hpartial := partial_le_exit_total φ (j + 1) hgood
    have htail := (depth_one_tail (j + 1)).2
    have hpow : (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ) - 1) = (2 : ℝ) ^ (-(j + 2 : ℤ)) := by
      congr 1
    rw [hpow] at htail
    have hasc := (symbolic_mass_summable φ).1.le_tsum j
      (fun i _ => ascendingMass_nonneg φ i)
    have hmass : ascendingMass φ j = (2 : ℝ) ^ (-(j + 2 : ℤ)) := by
      simp only [ascendingMass, ite_eq_left hj]
    rw [hmass] at hasc
    unfold symbolicFailureDensity
    linarith
  · have hgood : ∀ i : ℕ, ascendingGain φ (i + 2) < 0 := by
      intro i
      exact lt_of_not_ge (fun hi => hbad ⟨i, hi⟩)
    have hseries : depthOneSeries ≤ ∑' r : ℕ, ∑' k : ℕ, exitMass φ k r := by
      exact Summable.tsum_le_tsum
        (fun r => depthOneTerm_le_exit_row φ r (fun i _ => hgood i))
        depth_one_series_summable (landing_totals_summable φ)
    rw [exit_totals_comm φ] at hseries
    unfold symbolicFailureDensity
    linarith

/-- A failed ascending edge makes the universal bound strict, without an irrationality premise. -/
theorem depth_one_strict_of_bad_ascending (φ : Correction)
    (hbad : ∃ i : ℕ, 0 ≤ ascendingGain φ (i + 2)) :
    depthOneSeries < symbolicFailureDensity φ := by
  classical
  let j := Nat.find hbad
  have hj : 0 ≤ ascendingGain φ (j + 2) := Nat.find_spec hbad
  have hgood : ∀ i : ℕ, i + 1 < j + 1 → ascendingGain φ (i + 2) < 0 := by
    intro i hi
    exact lt_of_not_ge (Nat.find_min hbad (by omega))
  have hpartial := partial_le_exit_total φ (j + 1) hgood
  have htail : depthOneSeries - depthOnePartial (j + 1) <
      (2 : ℝ) ^ (-(j + 2 : ℤ)) := by
    convert depth_one_tail_strict (j + 1) using 1
    congr 1
  have hasc := (symbolic_mass_summable φ).1.le_tsum j
    (fun i _ => ascendingMass_nonneg φ i)
  have hmass : ascendingMass φ j = (2 : ℝ) ^ (-(j + 2 : ℤ)) := by
    simp only [ascendingMass, ite_eq_left hj]
  rw [hmass] at hasc
  unfold symbolicFailureDensity
  linarith

end ExternalO3DepthOneLower
