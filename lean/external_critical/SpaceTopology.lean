import CriticalSpaceExpectedTypes
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

/-! Proof evidence for the unchanged OnePoint/product/Borel topologies.
The convergent-sequence embedding is standard; no topology is redefined. -/
namespace ExternalCriticalSpaceTopology
open ExternalCriticalSpaceDraft MeasureTheory TopologicalSpace
open scoped Topology

noncomputable def heightEmbedding : Height → ℝ
  | OnePoint.infty => 0
  | OnePoint.some n => 1 / (n+1 : ℝ)

theorem height_embedding_continuous : Continuous heightEmbedding := by
  apply (OnePoint.continuous_iff_from_nat heightEmbedding).mpr
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem height_embedding_injective : Function.Injective heightEmbedding := by
  rintro (_ | n) (_ | m) h
  · rfl
  · have hp : (0 : ℝ) < 1/(m+1 : ℝ) := by positivity
    change 0 = 1/(m+1 : ℝ) at h
    linarith
  · have hp : (0 : ℝ) < 1/(n+1 : ℝ) := by positivity
    change 1/(n+1 : ℝ) = 0 at h
    linarith
  · change (1 : ℝ)/(n+1) = 1/(m+1) at h
    have he : (n : ℝ)+1 = (m : ℝ)+1 := by
      simpa only [one_div,inv_inj] using h
    have hn : n = m := by exact_mod_cast (add_right_cancel he)
    subst m
    rfl

theorem height_embedding_closed : IsClosedMap heightEmbedding := by
  intro s hs
  exact (hs.isCompact.image height_embedding_continuous).isClosed

theorem height_embedding_isClosedEmbedding : Topology.IsClosedEmbedding heightEmbedding :=
  .of_continuous_injective_isClosedMap height_embedding_continuous
    height_embedding_injective height_embedding_closed

instance heightMetrizable : MetrizableSpace Height :=
  height_embedding_isClosedEmbedding.isEmbedding.metrizableSpace

instance heightSecondCountable : SecondCountableTopology Height :=
  height_embedding_isClosedEmbedding.isEmbedding.secondCountableTopology

theorem uniform_phase_probability : IsProbabilityMeasure uniformPhase := by
  constructor
  simp [uniformPhase]

theorem space_topology : SpaceTopology := by
  exact ⟨inferInstance,inferInstance,inferInstance,inferInstance,uniform_phase_probability⟩

end ExternalCriticalSpaceTopology
