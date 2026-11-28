import WordTruncation

/-! Exact x-free tail recovery and finite truncation fiber bound. -/
namespace ExternalBridgePressureWordTruncationFiber
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressureWordPopulation
open ExternalBridgePressureWordTruncation
open scoped BigOperators

theorem truncate_letter_first (x : ℝ) (n m : ℕ) (w : Word (n+m))
    (hw : AuxWord x (n+m) w) (hn : 1 ≤ n) (i : Fin n) (hi : i.val+1<n) :
    truncateWord x n m w i = w (firstIndex n m i) := by
  have h := prefixLetters_cast n _ (truncate_profile_positive x n m w hw hn) i
  have ht : i.val<n := i.isLt
  simp only [truncateProfile,Fin.val_succ,Fin.val_castSucc,hi,ht,ite_true] at h
  have hs := wordPrefix_step (n+m) w (firstIndex n m i)
  change (truncateWord x n m w i : ℤ) =
    wordPrefix (n+m) w (firstIndex n m i).succ - wordPrefix (n+m) w (firstIndex n m i).castSucc at h
  rw [hs] at h
  exact_mod_cast (show (truncateWord x n m w i : ℤ) = (w (firstIndex n m i) : ℤ) by omega)

theorem tail_record_bound (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (w : Word (n+m)) (hw : AuxWord x (n+m) w) (i : Fin (m+1)) :
    n-1+i.val<n+m ∧ 1 ≤ tailRecord n m w i ∧ tailRecord n m w i ≤ 2*(n+m) ∧
      (boundedTailRecord n m w i).val = tailRecord n m w i := by
  have hi : n-1+i.val<n+m := by have := i.isLt; omega
  have hb := aux_word_letter_bounds x (n+m) hx w hw ⟨n-1+i.val,hi⟩
  have he : tailRecord n m w i = w ⟨n-1+i.val,hi⟩ := by
    unfold tailRecord letterAt
    split_ifs
    rfl
  refine ⟨hi,by rw [he]; exact hb.1,by rw [he]; exact hb.2,?_⟩
  exact Nat.mod_eq_of_lt (by rw [he]; omega)

theorem recover_long_word (x : ℝ) (n m : ℕ) (hn : 1 ≤ n)
    (w : Word (n+m)) (hw : AuxWord x (n+m) w) :
    recoverLongWord n m (truncateWord x n m w) (tailRecord n m w) = w := by
  funext i
  unfold recoverLongWord
  split_ifs with hi
  · have he := truncate_letter_first x n m w hw hn ⟨i.val,by omega⟩ hi
    exact he
  · have he : n-1+(i.val-(n-1))=i.val := by omega
    unfold tailRecord letterAt
    simp only [he,i.isLt,dite_true]

def recoverBoundedLongWord (n m : ℕ) (v : Word n)
    (a : Fin (m+1) → Fin (2*(n+m)+1)) : Word (n+m) :=
  recoverLongWord n m v (fun i => (a i).val)

theorem recover_bounded_long_word (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (w : Word (n+m)) (hw : AuxWord x (n+m) w) :
    recoverBoundedLongWord n m (truncateWord x n m w) (boundedTailRecord n m w) = w := by
  have he : (fun i => (boundedTailRecord n m w i).val) = tailRecord n m w := by
    funext i
    exact (tail_record_bound x n m hx hn w hw i).2.2.2
  unfold recoverBoundedLongWord
  rw [he]
  exact recover_long_word x n m hn w hw

theorem truncation_code_injective (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n) :
    Function.Injective (fun w : AuxWords x (n+m) => truncationCode x n m w.val) := by
  intro a b hab
  have h := congrArg (fun p => recoverBoundedLongWord n m p.1 p.2) hab
  simp only [truncationCode,recover_bounded_long_word x n m hx hn a.val a.property,
    recover_bounded_long_word x n m hx hn b.val b.property] at h
  exact Subtype.ext h

theorem truncation_fiber_encoding : TruncationFiberEncoding := by
  intro x n m hx hn
  refine ⟨truncation_code_injective x n m hx hn,fun w hw => ?_⟩
  exact ⟨recover_long_word x n m hn w hw,tail_record_bound x n m hx hn w hw⟩

theorem truncation_fiber_tail_injective (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (v : Word n) : Function.Injective
      (fun w : {w : AuxWords x (n+m) // truncateWord x n m w.val = v} => boundedTailRecord n m w.val.val) := by
  intro a b hab
  apply Subtype.ext
  apply truncation_code_injective x n m hx hn
  exact Prod.ext (a.property.trans b.property.symm) hab

theorem truncation_fiber_count : TruncationFiberCount := by
  intro x n m hx hn
  have hcard : Nat.card (Fin (m+1) → Fin (2*(n+m)+1)) = (2*(n+m)+1)^(m+1) := by
    simp only [Nat.card_fun,Nat.card_fin]
  refine ⟨hcard,fun v => ?_⟩
  have := aux_words_finite x (n+m) hx
  refine ⟨inferInstance,?_⟩
  calc
    Nat.card {w : AuxWords x (n+m) // truncateWord x n m w.val = v} ≤
        Nat.card (Fin (m+1) → Fin (2*(n+m)+1)) :=
      Nat.card_le_card_of_injective _ (truncation_fiber_tail_injective x n m hx hn v)
    _ = _ := hcard

end ExternalBridgePressureWordTruncationFiber
