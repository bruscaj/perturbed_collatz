import GeneralProjection
import GeneralCylinderDensity
import GeneralMarginal
import GeneralRefinementLabels
import GeneralGains

/-! Unconditional literal density for every fixed finite depth and arbitrary correction. -/
namespace ExternalO3GeneralDensity
open ExternalO3GeneralDraft ExternalO3GeneralWeights ExternalO3GeneralMarginal
open ExternalO3GeneralCylinderDensity ExternalO3GeneralRefinementLabels
open ExternalO3GeneralProjection ExternalO3GeneralGains Filter
open scoped Topology BigOperators

theorem coordinate_law : CoordinateLaw :=
  coordinate_law_of_refinement refined_cylinder_densities refined_label_cell
    refinement_projection_law coarse_marginal_law

theorem label_realizable : LabelRealizable := by
  classical
  intro h e
  by_contra hnone
  have hnot : ∀ n : ℕ, label h n ≠ e := by
    intro n hn
    exact hnone ⟨n, hn⟩
  have heq : populationFrequency (fun n => label h n = e) = fun _ => 0 := by
    funext N
    simp [populationFrequency, hnot]
  have hd := coordinate_law h e
  rw [heq] at hd
  have hz : (0 : ℝ) = weight h e := tendsto_nhds_unique tendsto_const_nhds hd
  exact (ne_of_gt (weight_positive h e)) hz.symm

theorem symbolic_density_bounds (h : Depth) (φ : Correction h) :
    0 ≤ symbolicFailureDensity h φ ∧ symbolicFailureDensity h φ ≤ 1 := by
  refine ⟨tsum_nonneg (selectedWeight_nonneg h φ), ?_⟩
  calc
    symbolicFailureDensity h φ ≤ ∑' e : Edge h, weight h e :=
      Summable.tsum_le_tsum (selectedWeight_le h φ) (selected_mass_summable h φ) (weight_summable h)
    _ = 1 := weight_tsum h

theorem density_equals_symbolic : DensityEqualsSymbolic := by
  classical
  intro h φ
  obtain ⟨hlo, hhi⟩ := symbolic_density_bounds h φ
  refine ⟨selected_mass_summable h φ, hlo, hhi, ?_⟩
  have hh := ExternalO3PartitionGeneral.countable_partition_density
    (label h) (fun n => FailsAt h φ (2 * n + 1)) (Bad h φ) (weight h)
    (weight_summable h) (weight_tsum h) (coordinate_law h) (cell_stabilization h φ)
  have hs : ExternalO3PartitionGeneral.selectedWeight (Bad h φ) (weight h) =
      selectedWeight h φ := by
    funext e
    by_cases hb : Bad h φ e <;>
      simp [ExternalO3PartitionGeneral.selectedWeight, selectedWeight, hb]
  rw [hs] at hh
  exact hh

theorem density_exists : DensityExists := by
  intro h φ
  have hh := density_equals_symbolic h φ
  exact ⟨symbolicFailureDensity h φ, hh.2.1, hh.2.2.1, hh.2.2.2⟩

end ExternalO3GeneralDensity
