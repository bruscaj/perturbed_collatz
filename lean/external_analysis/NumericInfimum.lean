import DepthOneFormula
import DepthOneNumerics

/-! Exact certificate linked to the infimum of actual literal failure densities. -/
namespace ExternalO3NumericInfimum
open ExternalO3Spec ExternalO3DepthOneNumerics ExternalO3DepthOneFormula

theorem failure_infimum_enclosure : seriesLower ≤ failureInfimum ∧ failureInfimum ≤ seriesUpper := by
  rw [show failureInfimum = depthOneSeries from depth_one_formula]
  exact series_enclosure

theorem failure_infimum_strict_upper : failureInfimum < seriesUpper := by
  rw [show failureInfimum = depthOneSeries from depth_one_formula]
  exact series_upper_strict

theorem certificate_width : seriesUpper - seriesLower = (2 : ℝ) ^ (-(81 : ℤ)) :=
  enclosure_width

end ExternalO3NumericInfimum
