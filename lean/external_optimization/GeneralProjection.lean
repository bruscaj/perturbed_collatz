import GeneralWeights
import PartitionGeneral

/-! Finite-tail transfer from exact refined population cells to coarse windows.
No countable additivity of natural density is used. -/
namespace ExternalO3GeneralProjection
open Filter ExternalO3GeneralDraft ExternalO3GeneralWeights
open scoped Topology BigOperators

/-- Pushforward of an exhaustive literal population partition via finite tails. -/
theorem pushforward_density {ι κ : Type*} (source : ℕ → ι) (project : ι → κ)
    (w : ι → ℝ) (hw : Summable w) (htotal : ∑' i, w i = 1)
    (hcell : ∀ i, Tendsto (ExternalO3CountablePartition.frequency
      (fun n => source n = i)) atTop (𝓝 (w i))) (e : κ) :
    Tendsto (ExternalO3CountablePartition.frequency (fun n => project (source n) = e))
      atTop (𝓝 (∑' i, ExternalO3PartitionGeneral.selectedWeight (fun j => project j = e) w i)) := by
  classical
  have h := ExternalO3PartitionGeneral.countable_partition_density
    source (fun n => project (source n) = e) (fun i => project i = e) w hw htotal
    hcell (fun i => ⟨0, fun n _ hn => by rw [hn]⟩)
  simpa only [ExternalO3PartitionGeneral.selectedWeight] using h

/-- Exact refined cylinders plus proved normalization supply the first tail transfer. -/
theorem coordinate_law_of_refinement
    (hclasses : RefinedCylinderDensities) (hlabel : RefinedLabelCell)
    (hproject : RefinementProjectionLaw) (hmarginal : CoarseMarginalLaw) :
    CoordinateLaw := by
  classical
  intro h e
  have hcells : ∀ data : RefinedIndex h.val,
      Tendsto (ExternalO3CountablePartition.frequency
        (fun n => refinedLabel h.val n = data)) atTop (𝓝 (refinedWeight h.val data)) := by
    intro data
    have hvalid : ValidBlockData h.val (decodedLengths h.val data) (decodedExits h.val data) := by
      constructor
      · intro i; simp [decodedLengths]
      · intro i; simp [decodedExits]
    have hp : (fun n => refinedLabel h.val n = data) =
        (fun n => RefinedCell h.val (decodedLengths h.val data)
          (decodedExits h.val data) (2 * n + 1)) := by
      funext n
      exact propext (hlabel h.val data n)
    have hh := hclasses h.val (decodedLengths h.val data) (decodedExits h.val data) hvalid
    change Tendsto (populationFrequency (fun n => refinedLabel h.val n = data))
      atTop (𝓝 (refinedWeight h.val data))
    rw [hp]
    exact hh
  have hh := pushforward_density (refinedLabel h.val) (refinementProjection h)
    (refinedWeight h.val) (refined_weight_summable h.val) (refined_weight_tsum h.val) hcells e
  have hp : (fun n => refinementProjection h (refinedLabel h.val n) = e) =
      (fun n => label h n = e) := by
    funext n
    rw [hproject h n]
  have hv : (∑' data : RefinedIndex h.val,
      ExternalO3PartitionGeneral.selectedWeight
        (fun i => refinementProjection h i = e) (refinedWeight h.val) data) = weight h e := by
    calc
      _ = ∑' data : RefinedIndex h.val, refinedFiberWeight h e data := by
        apply tsum_congr
        intro data
        by_cases hc : refinementProjection h data = e <;>
          simp [ExternalO3PartitionGeneral.selectedWeight, refinedFiberWeight, hc]
      _ = weight h e := (hmarginal h e).2
  rw [hp, hv] at hh
  exact hh

end ExternalO3GeneralProjection
