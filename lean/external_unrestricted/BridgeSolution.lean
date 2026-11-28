import BridgeArithmetic
import BridgeEncoding
import BridgeRungs
import BridgeRewards
import BridgeTransport
import BridgeFinite
import BridgeExtremal
import BridgeBoundary

/-! All twenty-five frozen finite source-word bridge targets. -/
namespace ExternalFiniteBridgeChallenge
open ExternalFiniteBridgeDraft

theorem finiteWordPrefixEncoding : FiniteWordPrefixEncoding :=
  ExternalFiniteBridgeEncoding.finite_word_prefix_encoding

theorem abstractPrefixCompatibility : AbstractPrefixCompatibility :=
  ExternalFiniteBridgeEncoding.abstract_prefix_compatibility

theorem defectBounds : DefectBounds := ExternalFiniteBridgeArithmetic.defect_bounds

theorem nonintegralEndpoint : NonintegralEndpoint :=
  ExternalFiniteBridgeArithmetic.nonintegral_endpoint

theorem strictRungCaps : StrictRungCaps := ExternalFiniteBridgeArithmetic.strict_rung_caps

theorem unitFloorIncrements : UnitFloorIncrements :=
  ExternalFiniteBridgeArithmetic.unit_floor_increments

theorem floorIncrementAlphabet : FloorIncrementAlphabet :=
  ExternalFiniteBridgeArithmetic.floor_increment_alphabet

theorem sourceSlopeFacts : SourceSlopeFacts := ExternalFiniteBridgeArithmetic.source_slope_facts

theorem sourceSlopeNonintegral : SourceSlopeNonintegral :=
  ExternalFiniteBridgeArithmetic.source_slope_nonintegral

theorem sourceRungsUnbounded : SourceRungsUnbounded :=
  ExternalFiniteBridgeRungs.source_rungs_unbounded

theorem literalClosingDepth : LiteralClosingDepth :=
  ExternalFiniteBridgeArithmetic.literal_closing_depth

theorem rewardEndpointInvariant : RewardEndpointInvariant :=
  ExternalFiniteBridgeRewards.reward_endpoint_invariant

theorem rewardRealPower : RewardRealPower := ExternalFiniteBridgeRewards.reward_real_power

theorem sourceDepthReward : SourceDepthReward := ExternalFiniteBridgeRewards.source_depth_reward

theorem referenceAtRungs : ReferenceAtRungs := ExternalFiniteBridgeRewards.reference_at_rungs

theorem sourceLastLetterLowerable : SourceLastLetterLowerable :=
  ExternalFiniteBridgeTransport.source_last_letter_lowerable

theorem lowerRaiseTransport : LowerRaiseTransport :=
  ExternalFiniteBridgeTransport.lower_raise_transport

theorem sourceFloorBijection : SourceFloorBijection :=
  ExternalFiniteBridgeTransport.source_floor_bijection

theorem finitePopulations : FinitePopulations := ExternalFiniteBridgeFinite.finite_populations

theorem sourceDepthBijection : SourceDepthBijection :=
  ExternalFiniteBridgeFinite.source_depth_bijection

theorem thresholdCountPreservation : ThresholdCountPreservation :=
  ExternalFiniteBridgeFinite.threshold_count_preservation

theorem phaseZeroExtremizer : PhaseZeroExtremizer :=
  ExternalFiniteBridgeExtremal.phase_zero_extremizer

theorem uniqueExtremizer : UniqueExtremizer := ExternalFiniteBridgeExtremal.unique_extremizer

theorem zeroLengthConvention : ZeroLengthConvention :=
  ExternalFiniteBridgeExtremal.zero_length_convention

theorem lengthOneBoundary : LengthOneBoundary := ExternalFiniteBridgeBoundary.length_one_boundary

end ExternalFiniteBridgeChallenge
