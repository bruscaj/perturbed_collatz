import AnalyticRotation

/-! Actual positive orbit density turns continuous forward domination into
constancy, retaining the closed auxiliary endpoint. -/
namespace ExternalBridgePressureAnalyticConstant
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft
open ExternalBridgePressureWordDraft ExternalBridgePressureAnalyticDraft
open ExternalBridgePressureAnalyticRotation Filter
open scoped Topology
noncomputable section

theorem phase_actual (x : ℝ) (m : ℕ) : ActualPhase (phaseShift x m) := by
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem orbit_approximation (x y : ℝ) (hx : ActualPhase x) (hy : ClosedPhase y) :
    ∃ m : ℕ → ℕ, (∀ k, 1 ≤ m k) ∧
      Tendsto (fun k => phaseShift x (m k)) atTop (𝓝 y) := by
  have hex (k : ℕ) := positive_rotation_orbit_dense x y hx hy
    (1 / ((k : ℝ)+1)) (by positivity)
  choose m hm using hex
  refine ⟨m, fun k => (hm k).1, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have ht : Tendsto (fun k : ℕ => (1 : ℝ)/((k : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [ht.eventually (gt_mem_nhds heps)] with k hk
  simpa only [Real.dist_eq] using ((hm k).2.trans hk)

theorem orbit_limit_value (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (x y : ℝ) (hy : ClosedPhase y) (m : ℕ → ℕ)
    (hm : Tendsto (fun k => phaseShift x (m k)) atTop (𝓝 y)) :
    Tendsto (fun k => f (phaseShift x (m k))) atTop (𝓝 (f y)) := by
  have hwithin : Tendsto (fun k => phaseShift x (m k)) atTop (𝓝[Set.Icc 0 1] y) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hm, Eventually.of_forall fun k => ?_⟩
    have h := phase_actual x (m k)
    exact ⟨h.1, le_of_lt h.2⟩
  have hcf : Tendsto f (𝓝[Set.Icc 0 1] y) (𝓝 (f y)) := hf y hy
  exact hcf.comp hwithin

theorem closed_value_le_actual (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (hdom : ∀ x : ℝ, ActualPhase x → ∀ m : ℕ, 1 ≤ m → f (phaseShift x m) ≤ f x)
    (x y : ℝ) (hx : ActualPhase x) (hy : ClosedPhase y) : f y ≤ f x := by
  obtain ⟨m, hm, hlim⟩ := orbit_approximation x y hx hy
  exact le_of_tendsto (orbit_limit_value f hf x y hy m hlim)
    (Eventually.of_forall fun k => hdom x hx (m k) (hm k))

theorem rotation_domination_implies_constant : RotationDominationImpliesConstant := by
  intro f hf hdom
  have hz : ActualPhase (0 : ℝ) := by constructor <;> norm_num
  have hzc : ClosedPhase (0 : ℝ) := ⟨hz.1, le_of_lt hz.2⟩
  have hactual (x : ℝ) (hx : ActualPhase x) : f x = f 0 := by
    exact le_antisymm
      (closed_value_le_actual f hf hdom 0 x hz ⟨hx.1, le_of_lt hx.2⟩)
      (closed_value_le_actual f hf hdom x 0 hx hzc)
  refine ⟨f 0, ?_⟩
  intro y hy
  obtain ⟨m, _hm, hlim⟩ := orbit_approximation 0 y hz hy
  have hfy := orbit_limit_value f hf 0 y hy m hlim
  have hfzero : Tendsto (fun k => f (phaseShift 0 (m k))) atTop (𝓝 (f 0)) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun k => (hactual _ (phase_actual _ _)).symm
  exact tendsto_nhds_unique hfy hfzero

end
end ExternalBridgePressureAnalyticConstant
