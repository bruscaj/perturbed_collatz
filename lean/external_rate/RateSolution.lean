import RateMain

/-! All11 required frozen statements; optional strongerliminf remains separate. -/
namespace ExternalO3RateChallenge
open ExternalO3RateDraft

theorem infimumWellPosed : InfimumWellPosed := ExternalO3RateInfimum.infimum_well_posed

theorem markerSelectorLaw : MarkerSelectorLaw := ExternalO3RateMarker.marker_selector_law

theorem markerUpperBound : MarkerUpperBound := ExternalO3RateMarkerEvents.marker_upper_bound

theorem historyWeightLaw : HistoryWeightLaw := ExternalO3RateMoments.history_weight_law

theorem cyclicNormalization : CyclicNormalization := ExternalO3RateNormalization.cyclic_normalization

theorem cyclicTelescoping : CyclicTelescoping := ExternalO3RateCycles.cyclic_telescoping

theorem cyclicForcing : CyclicForcing := ExternalO3RateCycles.cyclic_forcing

theorem cyclicDensityLowerBound : CyclicDensityLowerBound := ExternalO3RateLower.cyclic_density_lower_bound

theorem positiveCycleMassLowerBound : PositiveCycleMassLowerBound := ExternalO3RateCantelli.positive_cycle_mass_lower_bound

theorem explicitInverseDepthRate : ExplicitInverseDepthRate := ExternalO3RateMain.explicit_inverse_depth_rate

theorem infimumTendsToZero : InfimumTendsToZero := ExternalO3RateMain.infimum_tends_to_zero

end ExternalO3RateChallenge
