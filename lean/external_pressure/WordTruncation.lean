import WordPartitions

/-! Truncation closes at the original n-cap and preserves every open prefix. -/
namespace ExternalBridgePressureWordTruncation
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressureWordArithmetic
open ExternalBridgePressureWordReward ExternalBridgePressureWordPhysical
open scoped BigOperators

theorem truncate_profile_positive (x : ℝ) (n m : ℕ) (w : Word (n+m))
    (hw : AuxWord x (n+m) w) (hn : 1 ≤ n) : PositivePrefix n (truncateProfile x n m w) := by
  refine ⟨?_,fun i => ?_⟩
  · simp only [truncateProfile,Fin.val_zero,show 0<n by omega,ite_true]
    exact wordPrefix_zero (n+m) w
  · have hi : i.val<n := i.isLt
    have hip : i.val+1<n+m+1 := by omega
    have hs := (wordPrefix_positive (n+m) w hw.2.1).2 ⟨i.val,by omega⟩
    by_cases he : i.val+1<n
    · simp only [truncateProfile,Fin.val_succ,Fin.val_castSucc,hi,he,ite_true]
      exact hs
    · have hh : i.val+1=n := by omega
      have hb := aux_depth_nonneg x (n+m) w hw ⟨n,by omega⟩
      simp only [truncateProfile,Fin.val_succ,Fin.val_castSucc,hi,he,ite_true,ite_false]
      have hind : (⟨i.val,by omega⟩ : Fin (n+m)).succ = (⟨n,by omega⟩ : Fin (n+m+1)) := Fin.ext hh
      rw [hind] at hs
      change 0 ≤ auxCap x n - wordPrefix (n+m) w ⟨n,by omega⟩ at hb
      change wordPrefix (n+m) w ⟨i.val,by omega⟩ + 1 ≤ wordPrefix (n+m) w ⟨n,by omega⟩ at hs
      omega

theorem truncate_prefix (x : ℝ) (n m : ℕ) (w : Word (n+m))
    (hw : AuxWord x (n+m) w) (hn : 1 ≤ n) :
    wordPrefix n (truncateWord x n m w) = truncateProfile x n m w :=
  wordPrefix_prefixLetters n _ (truncate_profile_positive x n m w hw hn)

theorem truncate_word_legal (x : ℝ) (n m : ℕ) (w : Word (n+m))
    (hw : AuxWord x (n+m) w) (hn : 1 ≤ n) : AuxWord x n (truncateWord x n m w) := by
  refine ⟨by omega,prefixLetters_positive _ _ (truncate_profile_positive x n m w hw hn),?_,?_⟩
  · rw [truncate_prefix x n m w hw hn]
    simp [truncateProfile]
  · intro t
    rw [truncate_prefix x n m w hw hn]
    have ht : t.val<n := t.isLt
    simp only [truncateProfile,Fin.val_castSucc,ht,ite_true]
    have hb := aux_depth_nonneg x (n+m) w hw ⟨t.val,by omega⟩
    exact sub_nonneg.mp hb

theorem truncate_term_first (x : ℝ) (n m : ℕ) (w : Word (n+m))
    (hw : AuxWord x (n+m) w) (hn : 1 ≤ n) (t : Fin n) :
    auxTerm x n (truncateWord x n m w) t = auxTerm x (n+m) w (firstIndex n m t) := by
  unfold auxTerm
  rw [truncate_prefix x n m w hw hn]
  have hp : truncateProfile x n m w t.castSucc = wordPrefix (n+m) w (firstIndex n m t).castSucc := by
    unfold truncateProfile
    split_ifs with h
    · exact congrArg (wordPrefix (n+m) w) (Fin.ext rfl)
    · have := t.isLt
      simp only [Fin.val_castSucc] at h
      omega
  rw [hp]
  rfl

theorem truncate_reward_split (x : ℝ) (n m : ℕ) (w : Word (n+m))
    (hw : AuxWord x (n+m) w) (hn : 1 ≤ n) :
    auxReward x (n+m) w = auxReward x n (truncateWord x n m w) +
      ∑ t : Fin m, auxTerm x (n+m) w (Fin.natAdd n t) := by
  unfold auxReward
  rw [Fin.sum_univ_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  exact (truncate_term_first x n m w hw hn t).symm

theorem truncation_transport : TruncationTransport := by
  intro x n m hx hn w hw
  have ht := truncate_word_legal x n m w hw hn
  refine ⟨truncate_profile_positive x n m w hw hn,truncate_prefix x n m w hw hn,
    ht,truncate_term_first x n m w hw hn,?_,?_⟩
  · rw [truncate_reward_split x n m w hw hn]
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg (fun t _ => le_of_lt ((normalized_reward_law x (n+m) w hx hw).2.1 _).2.1)
  · rw [truncate_reward_split x n m w hw hn]
    apply add_le_add (le_refl _)
    calc
      (∑ t : Fin m, auxTerm x (n+m) w (Fin.natAdd n t)) ≤ ∑ _t : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => ((normalized_reward_law x (n+m) w hx hw).2.1 _).2.2)
      _ = (m : ℝ) := by simp

end ExternalBridgePressureWordTruncation
