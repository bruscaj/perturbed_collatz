import DepthOneSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Upper approximation for the literal h=1 correction infimum.
The proposed corrections approach the critical linear slope from above. Each
ascending failure disappears. Each exit decision converges to the mandatory
nonnegative-cycle decision, including exactly zero gains; no irrationality or
nonzero-cycle assumption is required. Summable source edge masses dominate
all selected exit weights, permitting Tannery's theorem.
-/
namespace ExternalO3DepthOneUpper

open ExternalO3Spec ExternalO3PopulationWeights ExternalO3DepthOneSeries Filter
open scoped Topology BigOperators

/-- Select a failure weight, retaining equality as a failure. -/
noncomputable def failureSelector (gain mass : ℝ) : ℝ := by
  classical
  exact if 0 ≤ gain then mass else 0

/-- Nonnegative perturbations tending to zero preserve the limiting failure
selector even when the limiting gain is exactly zero. -/
theorem nonnegative_selector_limit (g mass : ℝ) (u : ℕ → ℝ)
    (hu : ∀ n, 0 ≤ u n) (hzero : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => failureSelector (g + u n) mass) atTop
      (𝓝 (failureSelector g mass)) := by
  classical
  by_cases hg : 0 ≤ g
  · apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun n => by
      simp [failureSelector, hg, add_nonneg hg (hu n)])
  · have hneg : g < 0 := lt_of_not_ge hg
    have he : ∀ᶠ n in atTop, u n < -g :=
      (tendsto_order.1 hzero).2 (-g) (by linarith)
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    have hgn : ¬0 ≤ g + u n := by linarith
    simp [failureSelector, hg, hgn]

/-- The positive slope excess, with no exceptional zero denominator. -/
noncomputable def slopeExcess (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem slopeExcess_pos (n : ℕ) : 0 < slopeExcess n := by
  unfold slopeExcess
  positivity

theorem slopeExcess_tendsto_zero : Tendsto slopeExcess atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  change Tendsto (fun n => slopeExcess n) atTop (𝓝 0)
  simpa only [Function.comp_def, slopeExcess, Nat.cast_add, Nat.cast_one] using h

/-- A sequence of admissible, unrestricted finite-information corrections. -/
noncomputable def approximatingCorrection (n : ℕ) : Correction :=
  linearCorrection (ascent + slopeExcess n)

theorem linear_ascending_gain (c : ℝ) (r : ℕ) :
    ascendingGain (linearCorrection c) (r + 2) = ascent - c := by
  simp only [ascendingGain, linearCorrection, show r + 2 - 1 = r + 1 by omega,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  change ascent + ((r : ℝ) + 1 - 1) * c - ((r : ℝ) + 2 - 1) * c = ascent - c
  ring

theorem approximating_ascending_negative (n r : ℕ) :
    ascendingGain (approximatingCorrection n) (r + 2) < 0 := by
  unfold approximatingCorrection
  rw [linear_ascending_gain]
  have h := slopeExcess_pos n
  linarith

theorem approximating_ascending_mass_zero (n r : ℕ) :
    ascendingMass (approximatingCorrection n) r = 0 := by
  classical
  have hn : ¬0 ≤ ascendingGain (approximatingCorrection n) (r + 2) :=
    not_le.mpr (approximating_ascending_negative n r)
  simp [ascendingMass, hn]

theorem approximating_exit_gain (n k r : ℕ) :
    exitGain (approximatingCorrection n) (k + 2) (r + 1) =
      cycleGain (r + 1) (k + 2) + (r : ℝ) * slopeExcess n := by
  unfold approximatingCorrection
  rw [linear_exit_gain]
  ring

theorem exitMass_eq_selector (n k r : ℕ) :
    exitMass (approximatingCorrection n) k r =
      failureSelector (cycleGain (r + 1) (k + 2) + (r : ℝ) * slopeExcess n)
        (weight (.inr (k, r))) := by
  classical
  simp only [exitMass, approximating_exit_gain, failureSelector, weight]

theorem mandatoryMass_eq_selector (r k : ℕ) :
    mandatoryMass r k = failureSelector (cycleGain (r + 1) (k + 2))
      (weight (.inr (k, r))) := by
  rfl

/-- Zero cycle gains are retained: the approximating perturbation is nonnegative. -/
theorem exitMass_tendsto_mandatory (k r : ℕ) :
    Tendsto (fun n => exitMass (approximatingCorrection n) k r) atTop
      (𝓝 (mandatoryMass r k)) := by
  have hu : ∀ n, 0 ≤ (r : ℝ) * slopeExcess n :=
    fun n => mul_nonneg (Nat.cast_nonneg _) (slopeExcess_pos n).le
  have hz : Tendsto (fun n => (r : ℝ) * slopeExcess n) atTop (𝓝 0) := by
    simpa only [mul_zero] using slopeExcess_tendsto_zero.const_mul (r : ℝ)
  simpa only [exitMass_eq_selector, mandatoryMass_eq_selector] using
    nonnegative_selector_limit (cycleGain (r + 1) (k + 2))
      (weight (.inr (k, r))) (fun n => (r : ℝ) * slopeExcess n) hu hz

theorem approximating_exit_summable (n : ℕ) :
    Summable (fun p : ℕ × ℕ => exitMass (approximatingCorrection n) p.1 p.2) := by
  convert selected_exit_summable (approximatingCorrection n) using 1
  funext p
  rcases p with ⟨k, r⟩
  rfl

/-- A single summable source-weight bound dominates every approximating exit. -/
theorem exit_total_tendsto :
    Tendsto (fun n => ∑' p : ℕ × ℕ, exitMass (approximatingCorrection n) p.1 p.2)
      atTop (𝓝 (∑' p : ℕ × ℕ, mandatoryMass p.2 p.1)) := by
  apply tendsto_tsum_of_dominated_convergence exit_weight_summable
    (fun p => exitMass_tendsto_mandatory p.1 p.2)
  exact Eventually.of_forall (fun n p => by
    rcases p with ⟨k, r⟩
    have hlo : 0 ≤ exitMass (approximatingCorrection n) k r :=
      selectedWeight_nonneg (approximatingCorrection n) (.inr (k, r))
    have hle : exitMass (approximatingCorrection n) k r ≤ weight (.inr (k, r)) :=
      selectedWeight_le (approximatingCorrection n) (.inr (k, r))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlo] using hle)

/-- The ascending component is zero, so no mass is omitted by the exit sum. -/
theorem symbolic_eq_exit_total (n : ℕ) :
    symbolicFailureDensity (approximatingCorrection n) =
      ∑' p : ℕ × ℕ, exitMass (approximatingCorrection n) p.1 p.2 := by
  unfold symbolicFailureDensity
  simp only [approximating_ascending_mass_zero, tsum_zero, zero_add]
  exact (approximating_exit_summable n).tsum_prod.symm

/-- Reindexing the absolutely summable mandatory mass loses no exits. -/
theorem mandatory_exit_total_eq_rows :
    (∑' p : ℕ × ℕ, mandatoryMass p.2 p.1) =
      ∑' r : ℕ, ∑' k : ℕ, mandatoryMass r k := by
  calc
    (∑' p : ℕ × ℕ, mandatoryMass p.2 p.1) =
        ∑' p : ℕ × ℕ, mandatoryMass p.1 p.2 :=
      (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => mandatoryMass p.1 p.2)
    _ = ∑' r : ℕ, ∑' k : ℕ, mandatoryMass r k := mandatory_pair_summable.tsum_prod

/-- Strong symbolic approximation, prior to identifying the closed series. -/
theorem symbolic_tendsto_mandatory_rows :
    Tendsto (fun n => symbolicFailureDensity (approximatingCorrection n)) atTop
      (𝓝 (∑' r : ℕ, ∑' k : ℕ, mandatoryMass r k)) := by
  have h := exit_total_tendsto
  rw [mandatory_exit_total_eq_rows] at h
  simpa only [symbolic_eq_exit_total] using h

/-- Explicit linear corrections approach the independently identified series. -/
theorem symbolic_tendsto_series :
    Tendsto (fun n => symbolicFailureDensity (approximatingCorrection n)) atTop
      (𝓝 depthOneSeries) := by
  simpa only [mandatory_total_tsum] using symbolic_tendsto_mandatory_rows

/-- The required upper approximation, without assuming any infimum formula. -/
theorem symbolic_upper_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : Correction, symbolicFailureDensity φ < depthOneSeries + ε := by
  have he : ∀ᶠ n in atTop,
      symbolicFailureDensity (approximatingCorrection n) < depthOneSeries + ε :=
    (tendsto_order.1 symbolic_tendsto_series).2 (depthOneSeries + ε) (by linarith)
  obtain ⟨n, hn⟩ := he.exists
  exact ⟨approximatingCorrection n, hn⟩

end ExternalO3DepthOneUpper
