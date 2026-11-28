import RateBounds
import RateMarkerEvents

/-! Unconditional required rate and limit, assembled from the literal infimum proofs. -/
namespace ExternalO3RateMain
open ExternalO3RateDraft

theorem explicit_inverse_depth_rate : ExplicitInverseDepthRate :=
  ExternalO3RateBounds.explicit_rate_of_marker_upper
    ExternalO3RateMarkerEvents.marker_upper_bound

theorem infimum_tends_to_zero : InfimumTendsToZero :=
  ExternalO3RateInfimum.infimum_tends_to_zero_of_rate explicit_inverse_depth_rate

end ExternalO3RateMain
