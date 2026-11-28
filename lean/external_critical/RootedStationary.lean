import RootedShift

/-! Compactness of probability laws on the actual compactified configuration
space, with stationarity obtained from the proved finite-root boundary error. -/
namespace ExternalCriticalRootedStationary
open ExternalCriticalSpaceDraft ExternalCriticalSpaceTopology ExternalCriticalSpaceArithmetic
open ExternalCriticalRootedLaw ExternalCriticalRootedShift
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem rooted_stationary_subsequence : RootedStationarySubsequence := by
  intro n hn lam hlam
  let mu : ℕ → ProbabilityMeasure Config := fun k =>
    ⟨rootedMeasure (n k) (lam k), ⟨rooted_measure_univ (n k) (lam k) (by have := hn k; omega)⟩⟩
  refine ⟨mu, fun _ => rfl, ?_⟩
  obtain ⟨nu, phi, hphi, hlim⟩ := CompactSpace.tendsto_subseq mu
  refine ⟨phi, hphi, nu, hlim, ?_, ?_⟩
  · have hnlim : Tendsto (fun k => n (phi k)) atTop atTop := by
      apply tendsto_atTop.mpr
      intro R
      filter_upwards [eventually_ge_atTop R] with k hk
      have hp : k ≤ phi k := hphi.id_le k
      have hnk := hn (phi k)
      omega
    have hlim_map := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k => mu (phi k)) nu hlim (time_shift_continuous 1)
    have hlim_same : Tendsto (fun k => (mu (phi k)).map (timeShift 1)) atTop (𝓝 nu) := by
      apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
      intro f
      have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f
      have hb (w : Config) : |f w| ≤ ‖f‖ := by
        simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm w
      have hd : Tendsto (fun k =>
          (∫ w, f (timeShift 1 w) ∂(mu (phi k) : Measure Config))-
            (∫ w, f w ∂(mu (phi k) : Measure Config))) atTop (𝓝 0) := by
        apply squeeze_zero_norm
          (fun k => by
            simpa only [Real.norm_eq_abs, mu, Function.comp_apply, ProbabilityMeasure.coe_mk] using
              (root_shift_error (n (phi k)) (by have := hn (phi k); omega)
                (lam (phi k)) (hlam (phi k)) f f.continuous ‖f‖ (norm_nonneg _) hb))
          ((tendsto_const_div_atTop_nhds_zero_nat (2*‖f‖ : ℝ)).comp hnlim)
      have hsum := hd.add ht
      have he (k : ℕ) :
          (∫ w, f w ∂((mu (phi k)).map (timeShift 1) : Measure Config)) =
            ∫ w, f (timeShift 1 w) ∂(mu (phi k) : Measure Config) := by
        exact integral_map (time_shift_measurable 1).aemeasurable f.continuous.aestronglyMeasurable
      simpa only [he, Function.comp_apply, sub_add_cancel, zero_add] using hsum
    have he := tendsto_nhds_unique hlim_map hlim_same
    exact congrArg (fun p : ProbabilityMeasure Config => (p : Measure Config)) he
  · let phaseLaw : ProbabilityMeasure Phase := ⟨uniformPhase, uniform_phase_probability⟩
    have he (k : ℕ) : (mu k).map (Prod.fst : Config → Phase) = phaseLaw := by
      apply ProbabilityMeasure.toMeasure_injective
      exact rooted_measure_uniform_phase (n k) (lam k) (by have := hn k; omega)
    have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun k => mu (phi k)) nu hlim (continuous_fst : Continuous (Prod.fst : Config → Phase))
    simp_rw [he] at ht
    have heq := tendsto_nhds_unique ht tendsto_const_nhds
    exact congrArg (fun p : ProbabilityMeasure Phase => (p : Measure Phase)) heq

end
end ExternalCriticalRootedStationary
