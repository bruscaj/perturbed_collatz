import BridgeEncoding
import BridgeArithmetic

/-! Exact finite last-letter transport. All generic slope/rung/nonintegrality
premises are retained, and natural subtraction is justified before use. -/
namespace ExternalFiniteBridgeTransport
open ExternalFiniteBridgeDraft ExternalFiniteBridgeEncoding ExternalFiniteBridgeArithmetic
open scoped BigOperators

theorem wordPrefix_lower_interior (r : ℕ) (w : Word r) (t : Fin r) :
    wordPrefix r (lowerLast r w) t.castSucc = wordPrefix r w t.castSucc := by
  unfold wordPrefix
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit : i.val < t.val
  · have hi : i.val + 1 ≠ r := by have := t.isLt; omega
    simp only [Fin.val_castSucc, hit, ite_true, lowerLast, hi, ite_false]
  · simp only [Fin.val_castSucc, hit, ite_false]

theorem wordPrefix_raise_interior (r : ℕ) (w : Word r) (t : Fin r) :
    wordPrefix r (raiseLast r w) t.castSucc = wordPrefix r w t.castSucc := by
  unfold wordPrefix
  apply Finset.sum_congr rfl
  intro i _
  by_cases hit : i.val < t.val
  · have hi : i.val + 1 ≠ r := by have := t.isLt; omega
    simp only [Fin.val_castSucc, hit, ite_true, raiseLast, hi, ite_false]
  · simp only [Fin.val_castSucc, hit, ite_false]

theorem last_succ_eq (r : ℕ) (i : Fin r) (hi : i.val + 1 = r) :
    i.succ = Fin.last r := by
  apply Fin.ext
  exact hi

theorem wordPrefix_lower_last (r : ℕ) (w : Word r) (hr : 0 < r)
    (hw : ∀ i : Fin r, i.val + 1 = r → 1 ≤ w i) :
    wordPrefix r (lowerLast r w) (Fin.last r) = wordPrefix r w (Fin.last r) - 1 := by
  let i : Fin r := ⟨r - 1, by omega⟩
  have hi : i.val + 1 = r := by dsimp [i]; omega
  have his := last_succ_eq r i hi
  have hwi := hw i hi
  calc
    _ = wordPrefix r (lowerLast r w) i.succ := by rw [his]
    _ = wordPrefix r w i.castSucc + (w i : ℤ) - 1 := by
      rw [wordPrefix_step, wordPrefix_lower_interior]
      simp only [lowerLast, hi, ite_true, Nat.cast_sub hwi, Nat.cast_one]
      ring
    _ = _ := by rw [← his, wordPrefix_step]

theorem wordPrefix_raise_last (r : ℕ) (w : Word r) (hr : 0 < r) :
    wordPrefix r (raiseLast r w) (Fin.last r) = wordPrefix r w (Fin.last r) + 1 := by
  let i : Fin r := ⟨r - 1, by omega⟩
  have hi : i.val + 1 = r := by dsimp [i]; omega
  have his := last_succ_eq r i hi
  calc
    _ = wordPrefix r (raiseLast r w) i.succ := by rw [his]
    _ = wordPrefix r w i.castSucc + (w i : ℤ) + 1 := by
      rw [wordPrefix_step, wordPrefix_raise_interior]
      simp only [raiseLast, hi, ite_true, Nat.cast_add, Nat.cast_one]
      ring
    _ = _ := by rw [← his, wordPrefix_step]

theorem lower_raise_eq (r : ℕ) (w : Word r) : lowerLast r (raiseLast r w) = w := by
  funext i
  simp only [lowerLast, raiseLast]
  split_ifs <;> omega

theorem raise_lower_eq (r : ℕ) (w : Word r)
    (hw : ∀ i : Fin r, i.val + 1 = r → 1 ≤ w i) : raiseLast r (lowerLast r w) = w := by
  funext i
  simp only [lowerLast, raiseLast]
  split_ifs with hi
  · have := hw i hi
    omega
  · rfl

/-- The frozen last-letter lowerability target. -/
theorem source_last_letter_lowerable : SourceLastLetterLowerable := by
  intro θ r w hθ hr hni hw i hi
  have he := nonintegral_endpoint θ r hni
  have hc := hw.2.2.2 i
  rw [strict_rung_caps θ r hr i.val i.isLt] at hc
  have hu := unit_floor_increments θ hθ i.val
  rw [hi] at hu
  have hs := wordPrefix_step r w i
  rw [last_succ_eq r i hi, hw.2.2.1, he] at hs
  exact_mod_cast (show (2 : ℤ) ≤ (w i : ℤ) by omega)

theorem source_lower_floor (θ : ℝ) (r : ℕ) (w : Word r) (hθ : 1 ≤ θ)
    (hr : StrictRung θ r) (hni : NonIntegralAt θ r) (hw : SourceWord θ r w) :
    FloorWord θ r (lowerLast r w) := by
  have hlast := source_last_letter_lowerable θ r w hθ hr hni hw
  have hp : ∀ i : Fin r, i.val + 1 = r → 1 ≤ w i := fun i hi => by have := hlast i hi; omega
  have hend : wordPrefix r (lowerLast r w) (Fin.last r) = floorAt θ r := by
    rw [wordPrefix_lower_last r w hr.1 hp, hw.2.2.1, nonintegral_endpoint θ r hni]
    omega
  refine ⟨hr.1, ?_, hend, ?_⟩
  · intro i
    by_cases hi : i.val + 1 = r
    · have := hlast i hi
      simp only [lowerLast, hi, ite_true]
      omega
    · simpa only [lowerLast, hi, ite_false] using hw.2.1 i
  · intro t
    by_cases ht : t.val = r
    · have he : t = Fin.last r := Fin.ext ht
      rw [he, hend]
      exact le_rfl
    · have htr : t.val < r := by have := t.isLt; omega
      let i : Fin r := ⟨t.val, htr⟩
      have he : i.castSucc = t := by apply Fin.ext; rfl
      have hc := hw.2.2.2 i
      rw [strict_rung_caps θ r hr i.val i.isLt] at hc
      have hpref := wordPrefix_lower_interior r w i
      rw [he] at hpref
      rw [hpref]
      exact hc

theorem floor_raise_source (θ : ℝ) (r : ℕ) (w : Word r) (_hθ : 1 ≤ θ)
    (hr : StrictRung θ r) (hni : NonIntegralAt θ r) (hw : FloorWord θ r w) :
    SourceWord θ r (raiseLast r w) := by
  refine ⟨hr.1, ?_, ?_, ?_⟩
  · intro i
    have hp := hw.2.1 i
    simp only [raiseLast]
    split_ifs <;> omega
  · rw [wordPrefix_raise_last r w hr.1, hw.2.2.1, nonintegral_endpoint θ r hni]
  · intro t
    rw [wordPrefix_raise_interior, strict_rung_caps θ r hr t.val t.isLt]
    exact hw.2.2.2 t.castSucc

/-- The frozen two-way transport target with exact inverses. -/
theorem lower_raise_transport : LowerRaiseTransport := by
  intro θ r hθ hr hni
  constructor
  · intro w hw
    refine ⟨source_lower_floor θ r w hθ hr hni hw, raise_lower_eq r w ?_⟩
    intro i hi
    have := source_last_letter_lowerable θ r w hθ hr hni hw i hi
    omega
  · intro w hw
    exact ⟨floor_raise_source θ r w hθ hr hni hw, lower_raise_eq r w⟩

/-- The frozen finite subtype equivalence, with the prescribed underlying maps. -/
theorem source_floor_bijection : SourceFloorBijection := by
  intro θ r hθ hr hni
  let e : {w : Word r // SourceWord θ r w} ≃ {w : Word r // FloorWord θ r w} := {
    toFun := fun w => ⟨lowerLast r w.val, (lower_raise_transport θ r hθ hr hni).1 w.val w.property |>.1⟩
    invFun := fun w => ⟨raiseLast r w.val, (lower_raise_transport θ r hθ hr hni).2 w.val w.property |>.1⟩
    left_inv := fun w => Subtype.ext ((lower_raise_transport θ r hθ hr hni).1 w.val w.property |>.2)
    right_inv := fun w => Subtype.ext ((lower_raise_transport θ r hθ hr hni).2 w.val w.property |>.2) }
  exact ⟨e, fun _ => rfl, fun _ => rfl⟩

end ExternalFiniteBridgeTransport
