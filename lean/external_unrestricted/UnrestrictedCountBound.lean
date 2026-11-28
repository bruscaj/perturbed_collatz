import UnrestrictedCounts
import Mathlib.Combinatorics.Enumerative.Composition

namespace ExternalM4UnrestrictedCountBound
open ExternalM4UnrestrictedDraft ExternalFiniteBridgeDraft
open ExternalFiniteBridgeArithmetic ExternalFiniteBridgeFinite ExternalM4UnrestrictedCounts
open scoped BigOperators

noncomputable def selectedComposition (r : ℕ)
    (w : {w : Word r // SourceWord slope r w ∧ phaseZeroReference slope r ≤ reward r w}) :
    Composition (Int.ceil ((r : ℝ) * slope)).toNat where
  blocks := List.ofFn w.val
  blocks_pos := by
    intro i hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    exact w.property.1.2.1 j
  blocks_sum := by
    rw [List.sum_ofFn]
    have hz : ((∑ i : Fin r, w.val i : ℕ) : ℤ) = Int.ceil ((r : ℝ) * slope) := by
      simpa only [Nat.cast_sum] using
        (wordPrefix_last r w.val).symm.trans w.property.1.2.2.1
    exact_mod_cast congrArg Int.toNat hz

theorem selectedComposition_injective (r : ℕ) : Function.Injective (selectedComposition r) := by
  intro a b h
  apply Subtype.ext
  apply List.ofFn_injective
  exact congrArg (fun c : Composition (Int.ceil ((r : ℝ) * slope)).toNat => c.blocks) h

theorem count_upper (r : ℕ) : count r ≤ 2 ^ (2 * r) := by
  have hceil : Int.ceil ((r : ℝ) * slope) ≤ ((2 * r : ℕ) : ℤ) := by
    apply Int.ceil_le.mpr
    have hs := source_slope_facts.2.1
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    push_cast
    nlinarith
  have hn : (Int.ceil ((r : ℝ) * slope)).toNat - 1 ≤ 2 * r := by omega
  calc
    count r ≤ Nat.card (Composition (Int.ceil ((r : ℝ) * slope)).toNat) :=
      Nat.card_le_card_of_injective _ (selectedComposition_injective r)
    _ = 2 ^ ((Int.ceil ((r : ℝ) * slope)).toNat - 1) := by
      rw [Nat.card_eq_fintype_card, composition_card]
    _ ≤ 2 ^ (2 * r) := Nat.pow_le_pow_right (by decide) hn

theorem all_length_count_bounds : AllLengthCountBounds := by
  exact ⟨selected_finite, count_zero, fun r hr => ⟨count_pos r hr, count_upper r⟩⟩

end ExternalM4UnrestrictedCountBound
