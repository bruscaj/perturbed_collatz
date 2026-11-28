import UnrestrictedCanonical
import UnrestrictedSwaps
import UnrestrictedCounts

namespace ExternalM4UnrestrictedInjection
open ExternalM4UnrestrictedDraft ExternalFiniteBridgeDraft
open ExternalM4UnrestrictedCanonical ExternalM4UnrestrictedSwaps ExternalM4UnrestrictedCounts
open scoped BigOperators

theorem large_defect_witness_injection : LargeDefectWitnessInjection := by
  intro r hr hd
  obtain ⟨S, hS, hcard⟩ := many_disjoint_canonical_sites r hr
  refine ⟨S, hS, hcard, swap_family_injective r _ S hS, ?_⟩
  intro T
  have hT : AdmissibleSites r (canonicalWord r) T.val :=
    admissible_sites_subset r _ S T.val hS T.property
  have hsource := (canonical_all_length_word r (by omega)).1
  refine ⟨(swap_preserves_source r _ T.val hsource hT).2.2.2, ?_⟩
  have hloss := (canonical_swap_loss_bound r T.val hT).2.1
  have hsub : T.val.card ≤ S.card := Finset.card_le_card T.property
  have hn : 2 * (r / 8) ≤ r / 3 := by omega
  have hc : (T.val.card : ℝ) ≤ ((r / 3 : ℕ) : ℝ) / 2 := by
    have hsub' : (T.val.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hsub
    have hn' : 2 * ((r / 8 : ℕ) : ℝ) ≤ ((r / 3 : ℕ) : ℝ) := by exact_mod_cast hn
    rw [hcard] at hsub'
    linarith
  have hbudget := canonical_reward_budget r hd
  have hid := swap_reward_identity r _ T.val hT
  change phaseZeroReference slope r ≤ reward r (applySwaps r (canonicalWord r) T.val)
  linarith

theorem exponential_count_lower : ExponentialCountLower := by
  intro r hr hd
  obtain ⟨S, hS, hcard, hinj, hw⟩ := large_defect_witness_injection r hr hd
  let F : SwapCube r S → {w : Word r // SourceWord slope r w ∧
      phaseZeroReference slope r ≤ reward r w} :=
    fun T => ⟨swapFamily r (canonicalWord r) S T, hw T⟩
  let : Finite {w : Word r // SourceWord slope r w ∧
      phaseZeroReference slope r ≤ reward r w} := selected_finite r
  have hF : Function.Injective F := by
    intro a b h
    apply hinj
    exact congrArg (fun z : {w : Word r // SourceWord slope r w ∧
      phaseZeroReference slope r ≤ reward r w} => z.val) h
  have hle := Nat.card_le_card_of_injective F hF
  rw [swap_cube_card r S, hcard] at hle
  exact hle

end ExternalM4UnrestrictedInjection
