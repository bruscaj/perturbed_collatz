import BridgeArithmetic
import BridgeEncoding

/-! Exact length-one convention for the finite source dictionary. -/
namespace ExternalFiniteBridgeBoundary
open ExternalFiniteBridgeDraft ExternalFiniteBridgeArithmetic

theorem floor_one : floorAt slope 1 = 1 := by
  apply Int.floor_eq_iff.mpr
  norm_num only [Nat.cast_one, one_mul, Int.cast_one]
  constructor
  · exact source_slope_facts.1.le
  · linarith [source_slope_facts.2.1]

theorem ceil_one : Int.ceil (((1 : ℕ) : ℝ) * slope) = 2 := by
  rw [nonintegral_endpoint slope 1 (source_slope_nonintegral 1 (by omega)), floor_one]
  norm_num

theorem prefix_one_zero (w : Word 1) : wordPrefix 1 w 0 = 0 := by
  simp [wordPrefix]

theorem prefix_one_last (w : Word 1) : wordPrefix 1 w (Fin.last 1) = (w 0 : ℤ) := by
  simp [wordPrefix]

theorem source_one_iff (w : Word 1) : SourceWord slope 1 w ↔ w 0 = 2 := by
  constructor
  · intro hw
    have he := hw.2.2.1
    rw [prefix_one_last, ceil_one] at he
    exact_mod_cast he
  · intro hw
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [hi, hw]
    · rw [prefix_one_last, hw, ceil_one]
      norm_num
    · intro t
      have ht : t = 0 := Subsingleton.elim _ _
      subst t
      simpa [wordPrefix, literalCap] using
        (Int.floor_nonneg.mpr (defect_bounds slope 1).1)

theorem floor_word_one_iff (w : Word 1) : FloorWord slope 1 w ↔ w 0 = 1 := by
  constructor
  · intro hw
    have he := hw.2.2.1
    rw [prefix_one_last, floor_one] at he
    exact_mod_cast he
  · intro hw
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim _ _
      simp [hi, hw]
    · rw [prefix_one_last, hw, floor_one]
      norm_num
    · intro t
      have ht : t.val = 0 ∨ t.val = 1 := by omega
      rcases ht with ht | ht
      · have he : t = 0 := Fin.ext ht
        subst t
        simp [wordPrefix, floorAt]
      · have he : t = Fin.last 1 := Fin.ext ht
        subst t
        change wordPrefix 1 w (Fin.last 1) ≤ floorAt slope 1
        rw [prefix_one_last, hw, floor_one]
        norm_num

theorem reward_one (w : Word 1) : reward 1 w = 1 := by
  simp [reward, wordPrefix]

theorem bridge_depth_one (w : Word 1) (hw : SourceWord slope 1 w) :
    sourceBridgeDepth slope 1 w = fun _ => 0 := by
  have hw0 := (source_one_iff w).mp hw
  funext t
  have ht : t.val = 0 ∨ t.val = 1 := by omega
  rcases ht with ht | ht
  · have he : t = 0 := Fin.ext ht
    subst t
    simp [sourceBridgeDepth, wordDepth, wordPrefix, floorAt]
  · have he : t = Fin.last 1 := Fin.ext ht
    subst t
    change floorAt slope 1 - wordPrefix 1 (lowerLast 1 w) (Fin.last 1) = 0
    rw [floor_one, prefix_one_last]
    simp [lowerLast, hw0]

theorem reference_one : phaseZeroReference slope 1 = 1 := by
  simp [phaseZeroReference, floorAt]

theorem count_one : sourceCount 1 1 = 1 := by
  let e : {w : Word 1 // SourceWord slope 1 w ∧ (1 : ℝ) ≤ reward 1 w} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨fun _ => 2, (source_one_iff _).mpr rfl, by simp [reward_one]⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa [hi] using ((source_one_iff w.val).mp w.property.1).symm
      right_inv := by intro u; cases u; rfl }
  simpa [sourceCount] using Nat.card_congr e

theorem length_one_boundary : LengthOneBoundary := by
  refine ⟨⟨by omega, ?_⟩, source_one_iff, floor_word_one_iff, ?_, reference_one, count_one⟩
  · intro t ht hlt
    omega
  · intro w hw
    exact ⟨reward_one w, literal_closing_depth 1 w hw, bridge_depth_one w hw⟩

end ExternalFiniteBridgeBoundary
