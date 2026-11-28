import GeneralDensity
import GeneralSourceDensity
import GeneralCompatibility

/-! Implementations of all22 previously frozen statements; never imports GeneralChallenge. -/
namespace ExternalO3GeneralChallenge
open ExternalO3GeneralDraft

theorem blocksWellDefined : BlocksWellDefined := ExternalO3GeneralArithmetic.blocks_well_defined

theorem windowValidity : WindowValidity := ExternalO3GeneralArithmetic.window_validity

theorem windowTransport : WindowTransport := ExternalO3GeneralArithmetic.window_transport

theorem correctionRestriction : CorrectionRestriction := ExternalO3GeneralArithmetic.correction_restriction

theorem fixedPointAndZero : FixedPointAndZero := ExternalO3GeneralArithmetic.fixed_point_and_zero

theorem refinedCylinderClasses : RefinedCylinderClasses := ExternalO3GeneralBlockWords.refined_cylinder_classes

theorem refinedCylinderDensities : RefinedCylinderDensities := ExternalO3GeneralCylinderDensity.refined_cylinder_densities

theorem refinedLabelCell : RefinedLabelCell := ExternalO3GeneralRefinementLabels.refined_label_cell

theorem refinedWeightLaw : RefinedWeightLaw := ExternalO3GeneralWeights.refined_weight_law

theorem refinementProjectionLaw : RefinementProjectionLaw := ExternalO3GeneralRefinementLabels.refinement_projection_law

theorem coarseMarginalLaw : CoarseMarginalLaw := ExternalO3GeneralMarginal.coarse_marginal_law

theorem weightLaw : WeightLaw := ExternalO3GeneralWeights.weight_law

theorem coordinateLaw : CoordinateLaw := ExternalO3GeneralDensity.coordinate_law

theorem labelRealizable : LabelRealizable := ExternalO3GeneralDensity.label_realizable

theorem literalGainIdentity : LiteralGainIdentity := ExternalO3GeneralGains.literal_gain_identity

theorem cellStabilization : CellStabilization := ExternalO3GeneralGains.cell_stabilization

theorem selectedMassSummable : SelectedMassSummable := ExternalO3GeneralWeights.selected_mass_summable

theorem densityExists : DensityExists := ExternalO3GeneralDensity.density_exists

theorem densityEqualsSymbolic : DensityEqualsSymbolic := ExternalO3GeneralDensity.density_equals_symbolic

theorem densityUnique : DensityUnique := ExternalO3GeneralSourceDensity.density_unique

theorem sourceDensityEquivalence : SourceDensityEquivalence := ExternalO3GeneralSourceDensity.source_density_equivalence

theorem depthOneCompatibility : DepthOneCompatibility := ExternalO3GeneralCompatibility.depth_one_compatibility

end ExternalO3GeneralChallenge
