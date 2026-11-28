import RateExpectedTypes
import GeneralDensity
import GeneralSourceDensity

/-! The infimum is over literal achieved densities, without attainment assumptions. -/
namespace ExternalO3RateInfimum
open ExternalO3RateDraft ExternalO3GeneralDraft Filter
open scoped Topology

theorem infimum_well_posed : InfimumWellPosed := by
  intro h
  have hdens (φ : Correction h) : ∃! d : ℝ, HasFailureDensity h φ d := by
    obtain ⟨d, _, _, hd⟩ := ExternalO3GeneralDensity.density_exists h φ
    exact ⟨d, hd, fun e he => ExternalO3GeneralSourceDensity.density_unique h φ e d he hd⟩
  have hnonempty : (achievedDensities h).Nonempty := by
    obtain ⟨d, hd, _⟩ := hdens (fun _ => 0)
    exact ⟨d, (fun _ => 0), hd⟩
  have hbds : ∀ d ∈ achievedDensities h, 0 ≤ d ∧ d ≤ 1 := by
    rintro d ⟨φ, hd⟩
    exact ExternalO3GeneralSourceDensity.density_bounds h φ d hd
  exact ⟨hdens, hnonempty, ⟨0, fun d hd => (hbds d hd).1⟩, hbds⟩

theorem infimum_nonneg (h : Depth) : 0 ≤ failureInfimum h := by
  apply le_csInf (infimum_well_posed h).2.1
  intro d hd
  exact ((infimum_well_posed h).2.2.2 d hd).1

theorem infimum_le_density (h : Depth) (φ : Correction h) (d : ℝ)
    (hd : HasFailureDensity h φ d) : failureInfimum h ≤ d :=
  csInf_le (infimum_well_posed h).2.2.1 ⟨φ, hd⟩

theorem infimum_le_one (h : Depth) : failureInfimum h ≤ 1 := by
  obtain ⟨d, φ, hd⟩ := (infimum_well_posed h).2.1
  exact (infimum_le_density h φ d hd).trans
    (ExternalO3GeneralSourceDensity.density_bounds h φ d hd).2

theorem infimum_tends_to_zero_of_rate (hr : ExplicitInverseDepthRate) :
    InfimumTendsToZero := by
  have hs : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_atTop.2 (fun b => eventually_atTop.2 ⟨b, fun n hn => by omega⟩)
  have hi0 : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hi := hi0.comp hs
  have hu : Tendsto (fun n : ℕ => (5 : ℝ) / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    convert hi.const_mul ((5 : ℝ) / 2) using 1 <;>
      simp [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_assoc]
  apply squeeze_zero (fun n => infimum_nonneg (succDepth n)) ?_ hu
  intro n
  simpa [succDepth, Nat.cast_add, Nat.cast_one] using (hr (succDepth n)).2

end ExternalO3RateInfimum
