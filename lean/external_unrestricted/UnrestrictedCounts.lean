import UnrestrictedExpectedTypes
import BridgeExtremal
import BridgeFinite

namespace ExternalM4UnrestrictedCounts
open ExternalM4UnrestrictedDraft ExternalFiniteBridgeDraft
open ExternalFiniteBridgeArithmetic ExternalFiniteBridgeEncoding
open ExternalFiniteBridgeExtremal ExternalFiniteBridgeFinite
open scoped BigOperators

theorem selected_finite (r : ℕ) :
    Finite {w : Word r // SourceWord slope r w ∧
      phaseZeroReference slope r ≤ reward r w} := by
  let : Finite {w : Word r // SourceWord slope r w} := (finite_populations slope r).1
  exact Finite.of_injective
    (fun w : {w : Word r // SourceWord slope r w ∧
      phaseZeroReference slope r ≤ reward r w} =>
        (⟨w.val, w.property.1⟩ : {w : Word r // SourceWord slope r w}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {w : Word r // SourceWord slope r w} => z.val) h)

theorem rung_count_one : RungCountOne := by
  intro r hr
  change Nat.card {w : Word r // SourceWord slope r w ∧
    phaseZeroReference slope r ≤ reward r w} = 1
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨mechanicalWord slope r, mechanical_source r hr, ?_⟩, ?_⟩
  · exact (mechanical_reward r).ge
  · intro w
    apply Subtype.ext
    exact (unique_extremizer r hr w.val w.property.1).mp
      (le_antisymm (source_reward_le_reference r hr w.val w.property.1) w.property.2)

theorem count_zero : count 0 = 0 := by
  let : IsEmpty {w : Word 0 // SourceWord slope 0 w ∧
      phaseZeroReference slope 0 ≤ reward 0 w} :=
    ⟨by intro w; exact (Nat.lt_irrefl 0) w.property.1.1⟩
  exact Nat.card_of_isEmpty

theorem mechanical_source_all (r : ℕ) (hr : 0 < r) :
    SourceWord slope r (mechanicalWord slope r) := by
  refine ⟨hr, ?_, ?_, ?_⟩
  · exact raiseLast_positive r _ (prefixLetters_positive r _ (floorPrefix_positive r))
  · unfold mechanicalWord
    rw [raiseLast_prefix_last r hr, wordPrefix_prefixLetters r _ (floorPrefix_positive r)]
    change floorAt slope r + 1 = Int.ceil ((r : ℝ) * slope)
    exact (nonintegral_endpoint slope r (source_slope_nonintegral r hr)).symm
  · intro t
    rw [mechanical_prefix_open]
    unfold floorAt literalCap
    apply Int.floor_mono
    have hd := (defect_bounds slope r).1
    linarith

theorem count_pos (r : ℕ) (hr : 0 < r) : 1 ≤ count r := by
  change 0 < Nat.card {w : Word r // SourceWord slope r w ∧
    phaseZeroReference slope r ≤ reward r w}
  exact Nat.card_pos_iff.mpr ⟨⟨⟨mechanicalWord slope r,
    mechanical_source_all r hr, (mechanical_reward r).ge⟩⟩, selected_finite r⟩

end ExternalM4UnrestrictedCounts
