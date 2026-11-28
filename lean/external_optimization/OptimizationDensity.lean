import OptimizationDeletion
import OptimizationMass
import RateInfimum

/-! Restriction/extension bounds for the original literal achieved-density
infimum, and convergence at each fixed positive information depth. -/
namespace ExternalO3OptimizationDensity
open ExternalO3OptimizationDraft ExternalO3GeneralDraft
open ExternalO3OptimizationEncoding ExternalO3OptimizationMass ExternalO3OptimizationDeletion
open ExternalO3GeneralWeights Filter
open scoped BigOperators Topology
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_cost_as_retained_sum (h : Depth) (M J : ℕ) (φ : Correction h) :
    failureCost (truncatedGraph h M J) (fun v => φ (decodeVertex h M v)) =
      ∑ e ∈ retainedLabels h M J, selectedWeight h φ e := by
  classical
  unfold retainedLabels
  rw [Finset.sum_image (fun a _ b _ hab => edgeLabel_injective h M J hab)]
  unfold failureCost
  apply Finset.sum_congr rfl
  intro a _
  rw [corrected_gain]
  change (if 0 ≤ gain h φ (edgeLabel h M J a) then (rationalWeight h M J a : ℝ) else 0) = _
  rw [edge_weight]
  rfl

theorem retained_selected_summable (h : Depth) (M J : ℕ) (φ : Correction h) :
    Summable (fun e : Edge h => if Retained h M J e then selectedWeight h φ e else 0) := by
  classical
  apply Summable.of_nonneg_of_le
    (fun e => by split_ifs; exact selectedWeight_nonneg h φ e; exact le_rfl)
    (fun e => by split_ifs; exact le_rfl; exact selectedWeight_nonneg h φ e)
    (selected_mass_summable h φ)

theorem retained_selected_tsum (h : Depth) (M J : ℕ) (φ : Correction h) :
    (∑' e : Edge h, if Retained h M J e then selectedWeight h φ e else 0) =
      failureCost (truncatedGraph h M J) (fun v => φ (decodeVertex h M v)) := by
  classical
  rw [finite_cost_as_retained_sum]
  rw [tsum_eq_sum (s := retainedLabels h M J) (fun e he => by
    have hn : ¬ Retained h M J e := mt (retainedLabels_mem h M J e).mpr he
    simp only [hn, ite_false])]
  exact Finset.sum_congr rfl (fun e he => ite_eq_left ((retainedLabels_mem h M J e).mp he))

theorem finite_cost_le_symbolic (h : Depth) (M J : ℕ) (φ : Correction h) :
    failureCost (truncatedGraph h M J) (fun v => φ (decodeVertex h M v)) ≤ symbolicFailureDensity h φ := by
  rw [finite_cost_as_retained_sum]
  exact Summable.sum_le_tsum (retainedLabels h M J)
    (fun e _ => selectedWeight_nonneg h φ e) (selected_mass_summable h φ)

theorem symbolic_le_finite_cost_add_discarded (h : Depth) (M J : ℕ) (φ : Correction h) :
    symbolicFailureDensity h φ ≤
      failureCost (truncatedGraph h M J) (fun v => φ (decodeVertex h M v)) + discardedMass h M J := by
  classical
  have hp (e : Edge h) : selectedWeight h φ e ≤
      (if Retained h M J e then selectedWeight h φ e else 0) +
      (if Retained h M J e then 0 else weight h e) := by
    by_cases he : Retained h M J e
    · simp only [he, ite_true, add_zero, le_refl]
    · simpa only [he, ite_false, zero_add] using selectedWeight_le h φ e
  have hh := Summable.tsum_le_tsum hp (selected_mass_summable h φ)
    ((retained_selected_summable h M J φ).add (discarded_mask_summable h M J))
  rw [(retained_selected_summable h M J φ).tsum_add (discarded_mask_summable h M J),
    retained_selected_tsum] at hh
  exact hh

theorem finiteOptimum_le_symbolic (h : Depth) (M J : ℕ) (hM : 2 ≤ M) (hJ : 2 ≤ J)
    (φ : Correction h) : (finiteOptimum h M J : ℝ) ≤ symbolicFailureDensity h φ :=
  ((finite_optimization_exact h M J hM hJ).2.1 _).trans (finite_cost_le_symbolic h M J φ)

theorem finiteOptimum_le_literal_infimum (h : Depth) (M J : ℕ) (hM : 2 ≤ M) (hJ : 2 ≤ J) :
    (finiteOptimum h M J : ℝ) ≤ ExternalO3RateDraft.failureInfimum h := by
  apply le_csInf (ExternalO3RateInfimum.infimum_well_posed h).2.1
  rintro d ⟨φ, hd⟩
  have heq := ExternalO3GeneralSourceDensity.density_unique h φ d (symbolicFailureDensity h φ) hd
    (ExternalO3GeneralDensity.density_equals_symbolic h φ).2.2.2
  rw [heq]
  exact finiteOptimum_le_symbolic h M J hM hJ φ

theorem literal_infimum_le_finiteOptimum_add_tail (h : Depth) (M J : ℕ) (hM : 2 ≤ M) (hJ : 2 ≤ J) :
    ExternalO3RateDraft.failureInfimum h ≤ (finiteOptimum h M J : ℝ) + tailAllowance h M J := by
  obtain ⟨ψ, hψ⟩ := (finite_optimization_exact h M J hM hJ).2.2
  obtain ⟨φ, hφ⟩ := (vertex_encoding_and_extension h M hM).2.2 ψ
  have hrestriction : (fun v => φ (decodeVertex h M v)) = ψ := funext hφ
  have hupper := symbolic_le_finite_cost_add_discarded h M J φ
  rw [hrestriction, hψ] at hupper
  have htail := (discarded_mass_bound h M J hM hJ).2
  have hdensity := (ExternalO3GeneralDensity.density_equals_symbolic h φ).2.2.2
  have hinf := ExternalO3RateInfimum.infimum_le_density h φ (symbolicFailureDensity h φ) hdensity
  linarith

theorem literal_infimum_sandwich : LiteralInfimumSandwich := by
  intro h M J hM hJ
  exact ⟨finiteOptimum_le_literal_infimum h M J hM hJ,
    literal_infimum_le_finiteOptimum_add_tail h M J hM hJ⟩

theorem diagonal_tail_tends_to_zero (h : Depth) :
    Tendsto (fun n : ℕ => tailAllowance h (n + 2) (n + 2)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨b, fun n hn => by omega⟩)
  have hg : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hd : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, half_pow_eq_zpow] using hg.comp hs
  have hh := (hd.const_mul ((h.val : ℝ) + 1)).add hd
  simpa only [tailAllowance, mul_zero, add_zero] using hh

theorem diagonal_convergence : DiagonalConvergence := by
  intro h
  have hbound (n : ℕ) := literal_infimum_sandwich h (n + 2) (n + 2) (by omega) (by omega)
  have hg : Tendsto
      (fun n : ℕ => ExternalO3RateDraft.failureInfimum h - (finiteOptimum h (n + 2) (n + 2) : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (hbound n).1) ?_ (diagonal_tail_tends_to_zero h)
    intro n
    have hh := (hbound n).2
    linarith
  have hc : Tendsto (fun _ : ℕ => ExternalO3RateDraft.failureInfimum h) atTop
      (𝓝 (ExternalO3RateDraft.failureInfimum h)) := tendsto_const_nhds
  have hh := hc.sub hg
  simpa only [sub_sub_cancel, sub_zero] using hh

end
end ExternalO3OptimizationDensity
