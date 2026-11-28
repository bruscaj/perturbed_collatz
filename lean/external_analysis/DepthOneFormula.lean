import DensityTheorems
import DepthOneLower
import DepthOneUpper

/-! Infimum of actual literal failure densities, not a symbolic surrogate. -/
namespace ExternalO3DepthOneFormula
open ExternalO3Spec ExternalO3DensityTheorems ExternalO3DepthOneLower
open ExternalO3DepthOneUpper

theorem achieved_eq_symbolic (φ : Correction) (d : ℝ) (hd : HasFailureDensity φ d) :
    d = symbolicFailureDensity φ :=
  ExternalO3DensityBounds.density_unique φ d (symbolicFailureDensity φ)
    hd (density_equals_symbolic φ).2.2

theorem depth_one_formula : DepthOneFormula := by
  change failureInfimum = depthOneSeries
  apply le_antisymm
  · by_contra hn
    have hgap : 0 < (failureInfimum - depthOneSeries) / 2 := by linarith
    obtain ⟨φ, hφ⟩ := symbolic_upper_approximation
      ((failureInfimum - depthOneSeries) / 2) hgap
    have hm : symbolicFailureDensity φ ∈ achievedDensities :=
      ⟨φ, (density_equals_symbolic φ).2.2⟩
    have hi : failureInfimum ≤ symbolicFailureDensity φ :=
      csInf_le infimum_well_posed.2.1 hm
    linarith
  · apply le_csInf infimum_well_posed.1
    intro d hd
    obtain ⟨φ, hφ⟩ := hd
    rw [achieved_eq_symbolic φ d hφ]
    exact depth_one_lower φ

end ExternalO3DepthOneFormula
