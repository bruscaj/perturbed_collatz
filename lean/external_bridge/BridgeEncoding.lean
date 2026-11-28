import BridgeExpectedTypes

/-! Finite positive-letter/prefix encoding and exact restriction of the
previous abstract integer profile model. No rung or limit result is used. -/
namespace ExternalFiniteBridgeEncoding
open ExternalFiniteBridgeDraft
open scoped BigOperators

theorem wordPrefix_zero (r : ℕ) (w : Word r) : wordPrefix r w 0 = 0 := by
  simp [wordPrefix]

theorem wordPrefix_step (r : ℕ) (w : Word r) (i : Fin r) :
    wordPrefix r w i.succ = wordPrefix r w i.castSucc + (w i : ℤ) := by
  have hp (j : Fin r) : (if j.val < i.val + 1 then (w j : ℤ) else 0) =
      (if j.val < i.val then (w j : ℤ) else 0) + (if j = i then (w j : ℤ) else 0) := by
    by_cases he : j = i
    · subst j; simp
    · have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
      have hi : j.val < i.val + 1 ↔ j.val < i.val := by omega
      simp only [hi, he, ite_false, add_zero]
  unfold wordPrefix
  simp only [Fin.val_succ, Fin.val_castSucc]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun j _ => hp j)
  rw [Finset.sum_add_distrib] at hs
  simpa using hs

theorem wordPrefix_positive (r : ℕ) (w : Word r) (hw : PositiveWord r w) :
    PositivePrefix r (wordPrefix r w) := by
  refine ⟨wordPrefix_zero r w, fun i => ?_⟩
  rw [wordPrefix_step]
  have hi : (1 : ℤ) ≤ (w i : ℤ) := by exact_mod_cast hw i
  omega

theorem prefixLetters_wordPrefix (r : ℕ) (w : Word r) :
    prefixLetters r (wordPrefix r w) = w := by
  funext i
  simp [prefixLetters, wordPrefix_step]

theorem prefixLetters_cast (r : ℕ) (K : Prefix r) (hK : PositivePrefix r K) (i : Fin r) :
    (prefixLetters r K i : ℤ) = K i.succ - K i.castSucc := by
  have hi := hK.2 i
  simp only [prefixLetters, Int.toNat_of_nonneg (by omega : 0 ≤ K i.succ - K i.castSucc)]

theorem prefixLetters_positive (r : ℕ) (K : Prefix r) (hK : PositivePrefix r K) :
    PositiveWord r (prefixLetters r K) := by
  intro i
  have hi := hK.2 i
  have hc := prefixLetters_cast r K hK i
  exact_mod_cast (show (1 : ℤ) ≤ (prefixLetters r K i : ℤ) by omega)

theorem wordPrefix_prefixLetters (r : ℕ) (K : Prefix r) (hK : PositivePrefix r K) :
    wordPrefix r (prefixLetters r K) = K := by
  funext t
  induction t using Fin.induction with
  | zero => rw [wordPrefix_zero, hK.1]
  | succ i ih =>
    rw [wordPrefix_step, ih, prefixLetters_cast r K hK i]
    omega

/-- First exact frozen finite encoding target, including r=0. -/
theorem finite_word_prefix_encoding : FiniteWordPrefixEncoding :=
  ⟨fun r w hw => ⟨wordPrefix_positive r w hw, prefixLetters_wordPrefix r w⟩,
   fun r K hK => ⟨prefixLetters_positive r K hK, wordPrefix_prefixLetters r K hK⟩⟩

theorem extendPrefix_at (r : ℕ) (K : Prefix r) (t : Fin (r + 1)) :
    extendPrefix r K t.val = K t := by
  have ht : t.val ≤ r := by have := t.isLt; omega
  simp only [extendPrefix, ht, dite_true]

theorem extendPrefix_zero (r : ℕ) (K : Prefix r) : extendPrefix r K 0 = K 0 := by
  simpa only [Fin.val_zero] using extendPrefix_at r K 0

theorem extendPrefix_last (r : ℕ) (K : Prefix r) :
    extendPrefix r K r = K (Fin.last r) := by
  simpa only [Fin.val_last] using extendPrefix_at r K (Fin.last r)

theorem extendPrefix_castSucc (r : ℕ) (K : Prefix r) (i : Fin r) :
    extendPrefix r K i.val = K i.castSucc := by
  simpa only [Fin.val_castSucc] using extendPrefix_at r K i.castSucc

theorem extendPrefix_succ (r : ℕ) (K : Prefix r) (i : Fin r) :
    extendPrefix r K (i.val + 1) = K i.succ := by
  simpa only [Fin.val_succ] using extendPrefix_at r K i.succ

theorem extendPrefix_nat (r : ℕ) (K : Prefix r) (t : ℕ) (ht : t ≤ r) :
    extendPrefix r K t = K ⟨t, by omega⟩ := by
  simp only [extendPrefix, ht, dite_true]

/-- Exact compatibility with the previously frozen abstract integer predicates. -/
theorem abstract_prefix_compatibility : AbstractPrefixCompatibility := by
  constructor
  · intro θ r w hr
    constructor
    · rintro ⟨_, hw, hend, hcap⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [extendPrefix_zero, wordPrefix_zero]
      · rw [extendPrefix_last]
        exact hend
      · intro t ht
        have hi := (wordPrefix_positive r w hw).2 ⟨t, ht⟩
        rw [← extendPrefix_castSucc r (wordPrefix r w) ⟨t, ht⟩,
          ← extendPrefix_succ r (wordPrefix r w) ⟨t, ht⟩] at hi
        exact hi
      · intro t ht
        rw [extendPrefix_nat r _ t ht]
        exact hcap ⟨t, by omega⟩
    · rintro ⟨_, hend, hstep, hcap⟩
      refine ⟨hr, ?_, ?_, ?_⟩
      · intro i
        have hi := hstep i.val i.isLt
        rw [extendPrefix_castSucc r (wordPrefix r w) i, extendPrefix_succ r (wordPrefix r w) i,
          wordPrefix_step] at hi
        exact_mod_cast (show (1 : ℤ) ≤ (w i : ℤ) by omega)
      · rw [extendPrefix_last] at hend
        exact hend
      · intro t
        have hi := hcap t.val (by have := t.isLt; omega)
        rw [extendPrefix_at r _ t] at hi
        exact hi
  · intro θ r J
    constructor
    · rintro ⟨hz, hend, hpos, hstep⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [extendPrefix_zero]; exact hz
      · rw [extendPrefix_last]; exact hend
      · intro t ht
        rw [extendPrefix_nat r J t ht]
        exact hpos ⟨t, by omega⟩
      · intro t ht
        have hi := hstep ⟨t, ht⟩
        rw [← extendPrefix_castSucc r J ⟨t, ht⟩,
          ← extendPrefix_succ r J ⟨t, ht⟩] at hi
        exact hi
    · rintro ⟨hz, hend, hpos, hstep⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [extendPrefix_zero] at hz; exact hz
      · rw [extendPrefix_last] at hend; exact hend
      · intro t
        have hi := hpos t.val (by have := t.isLt; omega)
        rw [extendPrefix_at r _ t] at hi
        exact hi
      · intro i
        have hi := hstep i.val i.isLt
        rw [extendPrefix_castSucc r J i, extendPrefix_succ r J i] at hi
        exact hi

end ExternalFiniteBridgeEncoding
