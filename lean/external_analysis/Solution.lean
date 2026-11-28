import NumericInfimum
import DepthOneNonattainment

/-! Full h=1 implementations of the separately frozen challenge.
Challenge.lean is a specification with designated holes and is never imported. -/
namespace ExternalO3Challenge
open ExternalO3Spec

theorem valuationFoundation : ValuationFoundation := ExternalO3Arithmetic.valuation_foundation
theorem blockLengthLaw : BlockLengthLaw := ExternalO3Arithmetic.block_length_law
theorem fixedPointConvention : FixedPointConvention := ExternalO3Arithmetic.fixed_point_convention
theorem correctionZeroIrrelevant : CorrectionZeroIrrelevant := ExternalO3Arithmetic.correction_zero_irrelevant
theorem densityExists : DensityExists := ExternalO3DensityTheorems.density_exists
theorem densityUnique : DensityUnique := ExternalO3DensityBounds.density_unique
theorem sourceDensityEquivalence : SourceDensityEquivalence := ExternalO3SourceDensity.source_density_equivalence
theorem symbolicMassSummable : SymbolicMassSummable := ExternalO3PopulationWeights.symbolic_mass_summable
theorem densityEqualsSymbolic : DensityEqualsSymbolic := ExternalO3DensityTheorems.density_equals_symbolic
theorem infimumWellPosed : InfimumWellPosed := ExternalO3DensityTheorems.infimum_well_posed
theorem depthOneSeriesSummable : DepthOneSeriesSummable := ExternalO3DepthOneSeries.depth_one_series_summable
theorem depthOneFormula : DepthOneFormula := ExternalO3DepthOneFormula.depth_one_formula
theorem depthOneNotAttained : DepthOneNotAttained := ExternalO3DepthOneNonattainment.depth_one_not_attained
theorem depthOneTail : DepthOneTail := ExternalO3DepthOneSeries.depth_one_tail

end ExternalO3Challenge
