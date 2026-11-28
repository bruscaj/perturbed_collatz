import PopulationLabels
import DensityBounds
import SourceDensity

/-! Literal h=1 arbitrary-correction density. Infimum and nonattainment remain open. -/
namespace ExternalO3DensityTheorems
open ExternalO3Spec ExternalO3PopulationWeights ExternalO3PopulationLabels
open Filter
open scoped Topology

theorem density_equals_symbolic : DensityEqualsSymbolic := by
  intro φ
  obtain ⟨hlo, hhi⟩ := symbolic_density_bounds φ
  refine ⟨hlo, hhi, ?_⟩
  have h := ExternalO3PartitionGeneral.countable_partition_density
    label (fun n => FailsAt φ (2 * n + 1)) (Bad φ) weight
    weight_summable weight_tsum_one label_density (label_stabilizes φ)
  have heq : ExternalO3PartitionGeneral.selectedWeight (Bad φ) weight =
      ExternalO3PopulationWeights.selectedWeight φ := rfl
  rw [heq, selectedWeight_tsum_eq_symbolic φ] at h
  change Tendsto (fun N : ℕ => failureFrequency φ N) atTop
    (𝓝 (symbolicFailureDensity φ))
  change Tendsto (fun N : ℕ =>
    ExternalO3CountablePartition.frequency (fun n => FailsAt φ (2 * n + 1)) N)
      atTop (𝓝 (symbolicFailureDensity φ)) at h
  simpa only [failure_frequency_eq] using h

theorem density_exists : DensityExists := by
  intro φ
  obtain ⟨hlo, hhi, hd⟩ := density_equals_symbolic φ
  exact ⟨symbolicFailureDensity φ, hlo, hhi, hd⟩

theorem infimum_well_posed : InfimumWellPosed := by
  refine ⟨?_, ExternalO3DensityBounds.achieved_bounded_below, ?_⟩
  · let φ : Correction := fun _ => 0
    exact ⟨symbolicFailureDensity φ, φ, (density_equals_symbolic φ).2.2⟩
  · intro d hd
    obtain ⟨φ, hφ⟩ := hd
    exact ExternalO3DensityBounds.density_bounds φ d hφ

end ExternalO3DensityTheorems
