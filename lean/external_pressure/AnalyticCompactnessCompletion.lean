import AnalyticCompactness

namespace ExternalBridgePressureAnalyticCompactness
open ExternalBridgePressureAnalyticDraft ExternalBridgePressureWordDraft
open Filter Set
open scoped Topology
noncomputable section

theorem grid_to_uniform_cauchy : GridToUniformCauchy := by
  intro u hosc hgrid eps heps
  obtain ⟨delta, hd, N, _hN, hN⟩ := hosc (eps/3) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_gt (1/delta)
  have hmR : (0 : ℝ) < m := lt_trans (one_div_pos.mpr hd) hm
  have hmNat : 1 ≤ m := by exact_mod_cast hmR
  have hmesh : 1/(m : ℝ) < delta := by
    apply (div_lt_iff₀ hmR).2
    have := (div_lt_iff₀ hd).1 hm
    nlinarith
  have hpoints : ∀ i : Fin (m+1), ∃ K : ℕ, ∀ p ≥ K, ∀ q ≥ K,
      |u p (gridPoint m i)-u q (gridPoint m i)| < eps/3 := by
    intro i
    simpa only [Real.dist_eq] using (Metric.cauchySeq_iff.1 (hgrid m i)) (eps/3) (by positivity)
  choose K hK using hpoints
  let cutoff := max N (Finset.univ.sup K)
  refine ⟨cutoff, ?_⟩
  intro p q hp hq x hx
  obtain ⟨i, hi⟩ := (grid_mesh_cover m hmNat).2 x hx
  have hclose : |x-gridPoint m i| < delta := lt_of_le_of_lt hi hmesh
  have hpN : N ≤ p := le_trans (le_max_left _ _) hp
  have hqN : N ≤ q := le_trans (le_max_left _ _) hq
  have hKi : K i ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ i)
  have hpi : K i ≤ p := le_trans hKi (le_trans (le_max_right _ _) hp)
  have hqi : K i ≤ q := le_trans hKi (le_trans (le_max_right _ _) hq)
  have h1 := hN p hpN x (gridPoint m i) hx (grid_point_closed m i) hclose
  have h2 := hK i p hpi q hqi
  have h3 := hN q hqN x (gridPoint m i) hx (grid_point_closed m i) hclose
  have ht1 := abs_sub_le (u p x) (u p (gridPoint m i)) (u q x)
  have ht2 := abs_sub_le (u p (gridPoint m i)) (u q (gridPoint m i)) (u q x)
  rw [abs_sub_comm (u q (gridPoint m i)) (u q x)] at ht2
  linarith

theorem uniform_cauchy_continuous_limit : UniformCauchyContinuousLimit := by
  intro u hC hosc
  have hc : ∀ x : ℝ, ClosedPhase x → CauchySeq (fun n => u n x) := by
    intro x hx
    apply Metric.cauchySeq_iff.2
    intro eps heps
    obtain ⟨N, hN⟩ := hC eps heps
    refine ⟨N, ?_⟩
    intro p hp q hq
    simpa only [Real.dist_eq] using hN p q hp hq x hx
  have hex : ∀ x : ℝ, ∃ a : ℝ, ClosedPhase x →
      Tendsto (fun n => u n x) atTop (nhds a) := by
    intro x
    by_cases hx : ClosedPhase x
    · obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hc x hx)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => False.elim (hx h)⟩
  choose f hf using hex
  have huniform : UniformClosedConvergence u f := by
    intro eps heps
    obtain ⟨N, hN⟩ := hC (eps/2) (by positivity)
    refine ⟨max N 1, le_max_right _ _, ?_⟩
    intro n hn x hx
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hlim : Tendsto (fun q => |u n x-u q x|) atTop (nhds |u n x-f x|) :=
      (tendsto_const_nhds.sub (hf x hx)).abs
    have hle : |u n x-f x| ≤ eps/2 := le_of_tendsto hlim
      (eventually_atTop.2 ⟨N, fun q hq => (hN n q hnN hq x hx).le⟩)
    linarith
  refine ⟨f, ?_, huniform⟩
  apply Metric.continuousOn_iff.2
  intro x hx eps heps
  obtain ⟨delta, hd, N, _hN, hN⟩ := hosc (eps/3) (by positivity)
  obtain ⟨K, _hK, hK⟩ := huniform (eps/3) (by positivity)
  refine ⟨delta, hd, ?_⟩
  intro y hy hxy
  let n := max N K
  have hnear : |u n y-u n x| < eps/3 :=
    hN n (le_max_left _ _) y x hy hx (by simpa only [Real.dist_eq] using hxy)
  have hfy := hK n (le_max_right _ _) y hy
  have hfx := hK n (le_max_right _ _) x hx
  have ht1 := abs_sub_le (f y) (u n y) (f x)
  have ht2 := abs_sub_le (u n y) (u n x) (f x)
  rw [abs_sub_comm (f y) (u n y)] at ht1
  rw [Real.dist_eq]
  linarith

lemma equicontinuity_comp (u : FunctionSequence)
    (h : EventuallyEquicontinuousClosed u) (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) :
    EventuallyEquicontinuousClosed (fun n x => u (q n) x) := by
  intro eps heps
  obtain ⟨delta, hd, N, _hN, hN⟩ := h eps heps
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hq.eventually (eventually_ge_atTop N))
  refine ⟨delta, hd, max K 1, le_max_right _ _, ?_⟩
  intro n hn x y hx hy hxy
  exact hN (q n) (hK n (le_trans (le_max_left _ _) hn)) x y hx hy hxy

theorem discontinuous_sequence_compactness : DiscontinuousSequenceCompactness := by
  intro u hbound hosc s hs
  obtain ⟨k, hk, hgrid⟩ := dense_grid_subsequence u hbound s hs
  have hq : Tendsto (s ∘ k) atTop atTop := hs.comp hk.tendsto_atTop
  have heq := equicontinuity_comp u hosc (s ∘ k) hq
  have hC : UniformCauchyClosed (fun n x => u ((s ∘ k) n) x) := by
    apply grid_to_uniform_cauchy _ heq
    intro m i
    obtain ⟨a, ha⟩ := hgrid m i
    exact ha.cauchySeq
  obtain ⟨f, hf, huf⟩ := uniform_cauchy_continuous_limit _ hC heq
  exact ⟨k, hk, f, hf, huf⟩

end
end ExternalBridgePressureAnalyticCompactness
