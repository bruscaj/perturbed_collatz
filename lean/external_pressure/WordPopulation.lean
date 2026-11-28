import WordArithmetic
import Mathlib.Combinatorics.Enumerative.Composition

/-! Literal bounded-tuple coverage of positive auxiliary words. -/
namespace ExternalBridgePressureWordPopulation
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressureWordArithmetic
open scoped BigOperators

theorem word_letter_le_endpoint (n : ℕ) (w : Word n) (i : Fin n) :
    (w i : ℤ) ≤ wordPrefix n w (Fin.last n) := by
  have hs : (w i : ℤ) ≤ ∑ j : Fin n, (w j : ℤ) :=
    Finset.single_le_sum (f := fun j : Fin n => (w j : ℤ)) (fun j _ => by positivity) (Finset.mem_univ i)
  simpa [wordPrefix, Fin.isLt] using hs

theorem aux_word_letter_bounds (x : ℝ) (n : ℕ) (hx : ClosedPhase x)
    (w : Word n) (hw : AuxWord x n w) (i : Fin n) :
    1 ≤ w i ∧ w i ≤ 2*n := by
  refine ⟨hw.2.1 i, ?_⟩
  have h := word_letter_le_endpoint n w i
  rw [hw.2.2.1] at h
  have hu := aux_cap_upper x hx n (by have := hw.1; omega : 1 ≤ n)
  exact_mod_cast (le_trans h hu)

theorem decode_bounded_word_injective (n : ℕ) :
    Function.Injective (decodeBoundedWord n) := by
  intro a b hab
  funext i
  apply Fin.ext
  exact congrFun hab i

theorem bounded_word_enumeration : BoundedWordEnumeration := by
  refine ⟨decode_bounded_word_injective, ?_⟩
  intro x n hx w hw
  refine ⟨fun i => ⟨w i, by have := (aux_word_letter_bounds x n hx w hw i).2; omega⟩, rfl⟩

noncomputable def encodeAuxWord (x : ℝ) (n : ℕ) (hx : ClosedPhase x)
    (w : AuxWords x n) : BoundedWord n :=
  fun i => ⟨w.val i, by have := (aux_word_letter_bounds x n hx w.val w.property i).2; omega⟩

theorem encode_aux_word_injective (x : ℝ) (n : ℕ) (hx : ClosedPhase x) :
    Function.Injective (encodeAuxWord x n hx) := by
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun hab i)

theorem aux_words_finite (x : ℝ) (n : ℕ) (hx : ClosedPhase x) :
    Finite (AuxWords x n) :=
  Finite.of_injective (encodeAuxWord x n hx) (encode_aux_word_injective x n hx)


noncomputable def auxComposition (x : ℝ) (n : ℕ) (w : AuxWords x n) :
    Composition (auxCap x n).toNat where
  blocks := List.ofFn w.val
  blocks_pos := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact w.property.2.1 i
  blocks_sum := by
    rw [List.sum_ofFn]
    have h : ((∑ i : Fin n, w.val i : ℕ) : ℤ) = auxCap x n := by
      simpa [wordPrefix, Fin.isLt] using w.property.2.2.1
    simpa only [Int.toNat_natCast] using congrArg Int.toNat h

theorem aux_composition_injective (x : ℝ) (n : ℕ) :
    Function.Injective (auxComposition x n) := by
  intro a b hab
  apply Subtype.ext
  exact List.ofFn_injective (congrArg Composition.blocks hab)

theorem aux_words_card_le (x : ℝ) (n : ℕ) (hx : ClosedPhase x) :
    Nat.card (AuxWords x n) ≤ 4^n := by
  by_cases hn : 1 ≤ n
  swap
  · have hn0 : n = 0 := by omega
    subst n
    have : IsEmpty (AuxWords x 0) := ⟨fun w => by have := w.property.1; omega⟩
    simp
  have hu : (auxCap x n).toNat ≤ 2*n := by
    have h := aux_cap_upper x hx n hn
    exact Int.toNat_le.mpr (by exact_mod_cast h)
  calc
    Nat.card (AuxWords x n) ≤ Nat.card (Composition (auxCap x n).toNat) :=
      Nat.card_le_card_of_injective (auxComposition x n) (aux_composition_injective x n)
    _ = 2^((auxCap x n).toNat-1) := by rw [Nat.card_eq_fintype_card, composition_card]
    _ ≤ 2^(2*n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 4^n := by rw [Nat.pow_mul]

theorem finite_word_population : FiniteWordPopulation := by
  intro x n hx
  refine ⟨aux_words_finite x n hx, aux_words_card_le x n hx, ?_, ?_⟩
  · intro hn
    exact ⟨⟨canonicalWord x n, (canonical_word_law x n hx).2.2 hn⟩⟩
  · exact aux_word_letter_bounds x n hx

end ExternalBridgePressureWordPopulation
