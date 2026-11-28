import UnrestrictedRotation
import UnrestrictedCanonical
import UnrestrictedSwaps
import UnrestrictedInjection
import UnrestrictedCounts
import UnrestrictedCountBound
import UnrestrictedLimits

/-! Exact unconditional wrappers for the 23 frozen unrestricted-count targets. -/
namespace ExternalM4UnrestrictedChallenge
open ExternalM4UnrestrictedDraft

theorem slopeBounds : SlopeBounds :=
  ExternalM4UnrestrictedRotation.slope_bounds

theorem tripleRotationHighLow : TripleRotationHighLow :=
  ExternalM4UnrestrictedRotation.triple_rotation_high_low

theorem highPhaseCountLower : HighPhaseCountLower :=
  ExternalM4UnrestrictedRotation.high_phase_count_lower

theorem largeDefectsUnbounded : LargeDefectsUnbounded :=
  ExternalM4UnrestrictedRotation.large_defects_unbounded

theorem canonicalPrefixLaw : CanonicalPrefixLaw :=
  ExternalM4UnrestrictedCanonical.canonical_prefix_law

theorem canonicalAllLengthWord : CanonicalAllLengthWord :=
  ExternalM4UnrestrictedCanonical.canonical_all_length_word

theorem canonicalAlphabetAndSites : CanonicalAlphabetAndSites :=
  ExternalM4UnrestrictedCanonical.canonical_alphabet_and_sites

theorem manyDisjointCanonicalSites : ManyDisjointCanonicalSites :=
  ExternalM4UnrestrictedCanonical.many_disjoint_canonical_sites

theorem swapPrefixLaw : SwapPrefixLaw :=
  ExternalM4UnrestrictedSwaps.swap_prefix_law

theorem swapPreservesSource : SwapPreservesSource :=
  ExternalM4UnrestrictedSwaps.swap_preserves_source

theorem swapFamilyInjective : SwapFamilyInjective :=
  ExternalM4UnrestrictedSwaps.swap_family_injective

theorem swapCubeCard : SwapCubeCard :=
  ExternalM4UnrestrictedSwaps.swap_cube_card

theorem swapRewardIdentity : SwapRewardIdentity :=
  ExternalM4UnrestrictedSwaps.swap_reward_identity

theorem canonicalRewardBudget : CanonicalRewardBudget :=
  ExternalM4UnrestrictedCanonical.canonical_reward_budget

theorem canonicalSwapLossBound : CanonicalSwapLossBound :=
  ExternalM4UnrestrictedCanonical.canonical_swap_loss_bound

theorem largeDefectWitnessInjection : LargeDefectWitnessInjection :=
  ExternalM4UnrestrictedInjection.large_defect_witness_injection

theorem exponentialCountLower : ExponentialCountLower :=
  ExternalM4UnrestrictedInjection.exponential_count_lower

theorem rungCountOne : RungCountOne :=
  ExternalM4UnrestrictedCounts.rung_count_one

theorem allLengthCountBounds : AllLengthCountBounds :=
  ExternalM4UnrestrictedCountBound.all_length_count_bounds

theorem normalizedLogBounds : NormalizedLogBounds :=
  ExternalM4UnrestrictedLimits.normalized_log_bounds

theorem normalizedLogLiminf : NormalizedLogLiminf :=
  ExternalM4UnrestrictedLimits.normalized_log_liminf

theorem normalizedLogLimsup : NormalizedLogLimsup :=
  ExternalM4UnrestrictedLimits.normalized_log_limsup_of_exponential_count_lower
    ExternalM4UnrestrictedInjection.exponential_count_lower

theorem noAllLengthLimit : NoAllLengthLimit :=
  ExternalM4UnrestrictedLimits.no_all_length_limit_of_exponential_count_lower
    ExternalM4UnrestrictedInjection.exponential_count_lower

end ExternalM4UnrestrictedChallenge
