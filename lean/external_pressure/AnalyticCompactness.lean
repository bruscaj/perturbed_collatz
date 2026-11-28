import PressureAnalyticExpectedTypes
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic

namespace ExternalBridgePressureAnalyticCompactness
open ExternalBridgePressureAnalyticDraft ExternalBridgePressureWordDraft
open Filter Set
open scoped Topology
noncomputable section

lemma grid_point_closed (m : ℕ) (i : Fin (m+1)) : ClosedPhase (gridPoint m i) := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · by_cases hm : m = 0
    · simp [gridPoint, hm]
    · change (i.val : ℝ) / (m : ℝ) ≤ 1
      apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hm)).2
      exact_mod_cast Nat.le_of_lt_succ i.isLt

theorem grid_mesh_cover : GridMeshCover := by
  intro m hm
  refine ⟨grid_point_closed m, ?_⟩
  intro x hx
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let j : ℕ := ⌊x * (m : ℝ)⌋₊
  have hj0 : (j : ℝ) ≤ x * m := Nat.floor_le (mul_nonneg hx.1 hmR.le)
  have hj1 : x * (m : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  have hjm : j ≤ m := by
    have : (j : ℝ) ≤ m := by nlinarith [hx.2]
    exact_mod_cast this
  let i : Fin (m+1) := ⟨j, by omega⟩
  refine ⟨i, ?_⟩
  change |x - (j : ℝ)/(m : ℝ)| ≤ 1/(m : ℝ)
  have hlo : (j : ℝ)/(m : ℝ) ≤ x := (div_le_iff₀ hmR).2 hj0
  have hhi : x < ((j : ℝ)+1)/(m : ℝ) := (lt_div_iff₀ hmR).2 hj1
  rw [add_div] at hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

theorem dense_grid_subsequence : DenseGridSubsequence := by
  intro u hu s _hs
  rcases hu with ⟨M, _hM, hbound⟩
  let I := Σ m : ℕ, Fin (m+1)
  let K := Set.Icc (-M) M
  let X := {r : ℝ // r ∈ K}
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact K)
  let sequence : ℕ → I → X := fun n t =>
    ⟨u (s n) (gridPoint t.1 t.2), abs_le.mp (hbound _ _ (grid_point_closed _ _))⟩
  obtain ⟨f, k, hk, hconv⟩ := CompactSpace.tendsto_subseq sequence
  refine ⟨k, hk, ?_⟩
  intro m i
  refine ⟨(f ⟨m,i⟩).val, ?_⟩
  have hcoord := (continuous_apply (⟨m,i⟩ : I)).tendsto f |>.comp hconv
  have hvalue := continuous_subtype_val.tendsto (f ⟨m,i⟩) |>.comp hcoord
  simpa [sequence, Function.comp_def] using hvalue

end
end ExternalBridgePressureAnalyticCompactness
