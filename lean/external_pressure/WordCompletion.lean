import WordPartitions

/-! Completion of literal auxiliary words by the canonical cap tail. -/
namespace ExternalBridgePressureWordCompletion
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressureWordArithmetic
open ExternalBridgePressureWordReward ExternalBridgePressureWordPhysical
open scoped BigOperators

theorem complete_profile_at (x : ℝ) (n m : ℕ) (w : Word n)
    (t : Fin (n+1)) :
    completeProfile x n m w ⟨t.val,by have := t.isLt; omega⟩ = wordPrefix n w t := by
  simp only [completeProfile, show t.val ≤ n by have := t.isLt; omega, dite_true]

theorem complete_profile_positive (x : ℝ) (n m : ℕ) (_hx : ClosedPhase x) (_hn : 1 ≤ n)
    (w : Word n) (hw : AuxWord x n w) : PositivePrefix (n+m) (completeProfile x n m w) := by
  refine ⟨?_,fun i => ?_⟩
  · simp [completeProfile,wordPrefix_zero]
  · by_cases hi : i.val+1 ≤ n
    · have hi' : i.val<n := by omega
      have h := (wordPrefix_positive n w hw.2.1).2 ⟨i.val,hi'⟩
      simp only [completeProfile,Fin.val_succ,Fin.val_castSucc,hi,
        show i.val ≤ n by omega,dite_true]
      exact h
    · by_cases he : i.val ≤ n
      · have hin : i.val=n := by omega
        have hc := aux_cap_increment x n
        have hlast : (⟨i.val,by omega⟩ : Fin (n+1)) = Fin.last n := Fin.ext hin
        simp only [completeProfile,Fin.val_succ,Fin.val_castSucc,hi,he,dite_false,dite_true]
        rw [hlast,hw.2.2.1,hin]
        omega
      · have hc := aux_cap_increment x i.val
        simp only [completeProfile,Fin.val_succ,Fin.val_castSucc,hi,he,dite_false]
        omega

theorem complete_prefix (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (w : Word n) (hw : AuxWord x n w) :
    wordPrefix (n+m) (completeWord x n m w) = completeProfile x n m w :=
  wordPrefix_prefixLetters (n+m) _ (complete_profile_positive x n m hx hn w hw)

theorem complete_word_legal (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (w : Word n) (hw : AuxWord x n w) : AuxWord x (n+m) (completeWord x n m w) := by
  refine ⟨by omega,prefixLetters_positive _ _ (complete_profile_positive x n m hx hn w hw),?_,?_⟩
  · rw [complete_prefix x n m hx hn w hw]
    unfold completeProfile
    split_ifs with h
    · have hm : m=0 := by have := Fin.val_last (n+m); simp only [Fin.val_last] at h; omega
      subst m
      exact hw.2.2.1
    · rfl
  · intro t
    rw [complete_prefix x n m hx hn w hw]
    unfold completeProfile
    split_ifs with h
    · have hc := aux_depth_nonneg x n w hw ⟨t.val,by simp only [Fin.val_castSucc] at h; omega⟩
      unfold auxDepth at hc
      exact sub_nonneg.mp hc
    · exact le_refl _

theorem complete_letters_first (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (w : Word n) (hw : AuxWord x n w) (i : Fin n) :
    completeWord x n m w (firstIndex n m i) = w i := by
  have hp := complete_profile_positive x n m hx hn w hw
  have h := prefixLetters_cast (n+m) _ hp (firstIndex n m i)
  have hstep := wordPrefix_step n w i
  have hleft : (firstIndex n m i).val ≤ n := by simp only [firstIndex]; have := i.isLt; omega
  have hright : (firstIndex n m i).val+1 ≤ n := by simp only [firstIndex]; have := i.isLt; omega
  simp only [completeProfile,Fin.val_succ,Fin.val_castSucc,hleft,hright,dite_true] at h
  change (completeWord x n m w (firstIndex n m i) : ℤ) =
    wordPrefix n w i.succ-wordPrefix n w i.castSucc at h
  rw [hstep] at h
  exact_mod_cast (show (completeWord x n m w (firstIndex n m i) : ℤ) = (w i : ℤ) by omega)

theorem complete_word_injective (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n) :
    Function.Injective (fun w : AuxWords x n => completeWord x n m w.val) := by
  intro a b hab
  apply Subtype.ext
  funext i
  have h := congrFun hab (firstIndex n m i)
  simpa only [complete_letters_first x n m hx hn a.val a.property i,
    complete_letters_first x n m hx hn b.val b.property i] using h

theorem complete_term_first (x : ℝ) (n m : ℕ) (hx : ClosedPhase x) (hn : 1 ≤ n)
    (w : Word n) (hw : AuxWord x n w) (t : Fin n) :
    auxTerm x (n+m) (completeWord x n m w) (firstIndex n m t) = auxTerm x n w t := by
  unfold auxTerm
  rw [complete_prefix x n m hx hn w hw]
  have hi : completeProfile x n m w (firstIndex n m t).castSucc = wordPrefix n w t.castSucc := by
    have ht : t.val ≤ n := by have := t.isLt; omega
    dsimp only [completeProfile,firstIndex,Fin.castSucc]
    split_ifs with h
    · exact congrArg (wordPrefix n w) (Fin.ext rfl)
    · simp only [Fin.val_castAdd] at h
      omega
  change Real.rpow 2 (-x) * ((2 : ℝ)^completeProfile x n m w (firstIndex n m t).castSucc /
    (3 : ℝ)^t.val) = _
  rw [hi]

theorem completion_transport : CompletionTransport := by
  intro x n m hx hn
  refine ⟨complete_word_injective x n m hx hn,fun w hw => ?_⟩
  have hlegal := complete_word_legal x n m hx hn w hw
  refine ⟨complete_profile_positive x n m hx hn w hw,complete_prefix x n m hx hn w hw,
    hlegal,complete_term_first x n m hx hn w hw,?_⟩
  apply Finset.sum_le_sum_of_injOn (firstIndex n m)
  · intro a _ b _ hab
    exact Fin.ext (congrArg (fun z : Fin (n+m) => z.val) hab)
  · intro _ _
    exact Finset.mem_univ _
  · intro t _
    exact le_of_eq (complete_term_first x n m hx hn w hw t).symm
  · intro t _ _
    exact le_of_lt ((normalized_reward_law x (n+m) _ hx hlegal).2.1 t).2.1

end ExternalBridgePressureWordCompletion
