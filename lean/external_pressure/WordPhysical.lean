import WordReward
import WordPopulation
import PhasePaths

/-! Actual-phase natural-depth completeness and exact finite word/path dictionary. -/
namespace ExternalBridgePressureWordPhysical
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalFiniteBridgeEncoding ExternalBridgePressurePaths
open ExternalBridgePressureWordReward
open scoped BigOperators

theorem actual_cap_zero (x : ℝ) (hx : ActualPhase x) : auxCap x 0 = 0 := by
  have hu : Int.floor x < 1 := Int.floor_lt.mpr (by simpa using hx.2)
  have hl := Int.floor_nonneg.mpr hx.1
  simpa [auxCap] using (show Int.floor x = 0 by omega)

theorem actual_phase_floor (x : ℝ) (hx : ActualPhase x) (t : ℕ) :
    phaseFloor x t = auxCap x t := by
  have hz := actual_cap_zero x hx
  simp only [auxCap, Nat.cast_zero, zero_mul, add_zero] at hz
  simp [phaseFloor, auxCap, hz]

theorem natural_depth_completeness : NaturalDepthCompleteness := by
  intro x n _ j hj t
  exact (natural_depth_bound x n j hj t).trans (by have := t.isLt; omega)

theorem aux_depth_nonneg (x : ℝ) (n : ℕ) (w : Word n)
    (hw : AuxWord x n w) (t : Fin (n+1)) : 0 ≤ auxDepth x n w t := by
  unfold auxDepth
  induction t using Fin.lastCases with
  | last => simpa only [Fin.val_last, hw.2.2.1, sub_self] using (le_refl (0 : ℤ))
  | cast i => exact sub_nonneg.mpr (hw.2.2.2 i)

theorem aux_depth_natural_legal (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (w : Word n) (hw : AuxWord x n w) :
    NaturalPathLegal x n (fun t => (auxDepth x n w t).toNat) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [auxDepth, actual_cap_zero x hx, wordPrefix_zero]
  · simp [auxDepth, hw.2.2.1]
  · intro i
    rw [Int.toNat_of_nonneg (aux_depth_nonneg x n w hw i.succ),
      Int.toNat_of_nonneg (aux_depth_nonneg x n w hw i.castSucc)]
    have hpos : (1 : ℤ) ≤ (w i : ℤ) := by exact_mod_cast hw.2.1 i
    simp only [auxDepth, wordPrefix_step, Fin.val_succ, Fin.val_castSucc,
      phaseIncrement, actual_phase_floor x hx]
    omega

theorem word_to_path_value (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (w : Word n) (hw : AuxWord x n w) (t : Fin (n+1)) :
    ((wordToPath x n w t).val : ℤ) = auxDepth x n w t := by
  have hb := natural_depth_completeness x n hx _ (aux_depth_natural_legal x n hx w hw) t
  have hl : (auxDepth x n w t).toNat < n+1 := by omega
  simp only [wordToPath, Nat.mod_eq_of_lt hl,
    Int.toNat_of_nonneg (aux_depth_nonneg x n w hw t)]

theorem word_to_path_legal (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (w : Word n) (hw : AuxWord x n w) : PathLegal x n (wordToPath x n w) := by
  have h := aux_depth_natural_legal x n hx w hw
  have he : (fun t => (wordToPath x n w t).val) = fun t => (auxDepth x n w t).toNat := by
    funext t
    have := word_to_path_value x n hx w hw t
    omega
  unfold PathLegal
  rw [he]
  exact h

theorem path_profile_positive (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (j : Path n) (hj : PathLegal x n j) :
    PositivePrefix n (fun t => auxCap x t.val - ((j t).val : ℤ)) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [actual_cap_zero x hx, hj.1]
  · have h := hj.2.2 i
    simp only [phaseIncrement, actual_phase_floor x hx] at h
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega

theorem path_to_word_prefix (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (j : Path n) (hj : PathLegal x n j) :
    wordPrefix n (pathToWord x n j) = fun t => auxCap x t.val - ((j t).val : ℤ) :=
  wordPrefix_prefixLetters n _ (path_profile_positive x n hx j hj)

theorem path_to_word_legal (x : ℝ) (n : ℕ) (hx : ActualPhase x) (hn : 1 ≤ n)
    (j : Path n) (hj : PathLegal x n j) : AuxWord x n (pathToWord x n j) := by
  refine ⟨by omega, prefixLetters_positive n _ (path_profile_positive x n hx j hj), ?_, ?_⟩
  · rw [path_to_word_prefix x n hx j hj]
    simp [hj.2.1]
  · intro t
    rw [path_to_word_prefix x n hx j hj]
    simp only [Fin.val_castSucc]
    omega

theorem path_to_word_to_path (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (w : Word n) (hw : AuxWord x n w) : pathToWord x n (wordToPath x n w) = w := by
  have hprof : (fun t => auxCap x t.val - ((wordToPath x n w t).val : ℤ)) = wordPrefix n w := by
    funext t
    rw [word_to_path_value x n hx w hw t]
    simp [auxDepth]
  unfold pathToWord
  rw [hprof, prefixLetters_wordPrefix]

theorem word_to_path_to_word (x : ℝ) (n : ℕ) (hx : ActualPhase x) (hn : 1 ≤ n)
    (j : Path n) (hj : PathLegal x n j) : wordToPath x n (pathToWord x n j) = j := by
  funext t
  apply Fin.ext
  have h := word_to_path_value x n hx _ (path_to_word_legal x n hx hn j hj) t
  unfold auxDepth at h
  rw [path_to_word_prefix x n hx j hj] at h
  dsimp only at h
  omega

theorem word_path_reward (x : ℝ) (n : ℕ) (hx : ActualPhase x)
    (w : Word n) (hw : AuxWord x n w) :
    auxReward x n w = pathReward x n (wordToPath x n w) := by
  apply Finset.sum_congr rfl
  intro t _
  rw [aux_term_real_power, word_to_path_value x n hx w hw]
  unfold phaseWeight
  simp only [Real.rpow_eq_pow]
  erw [← Real.rpow_intCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  simp only [phaseTick, Int.fract, auxDepth, auxCap, Fin.val_castSucc]
  push_cast
  ring

noncomputable def wordPathEquiv (x : ℝ) (n : ℕ) (hx : ActualPhase x) (hn : 1 ≤ n) :
    AuxWords x n ≃ {j : Path n // PathLegal x n j} where
  toFun w := ⟨wordToPath x n w.val, word_to_path_legal x n hx w.val w.property⟩
  invFun j := ⟨pathToWord x n j.val, path_to_word_legal x n hx hn j.val j.property⟩
  left_inv w := Subtype.ext (path_to_word_to_path x n hx w.val w.property)
  right_inv j := Subtype.ext (word_to_path_to_word x n hx hn j.val j.property)

theorem word_depth_dictionary : WordDepthDictionary := by
  intro x n hx hn
  refine ⟨?_, ?_, wordPathEquiv x n hx hn, fun _ => rfl, fun _ => rfl⟩
  · intro w hw
    refine ⟨fun t => ?_, word_to_path_legal x n hx w hw,
      path_to_word_to_path x n hx w hw, word_path_reward x n hx w hw⟩
    have h := natural_depth_completeness x n hx _ (aux_depth_natural_legal x n hx w hw) t
    have he := word_to_path_value x n hx w hw t
    exact ⟨aux_depth_nonneg x n w hw t, by omega, he⟩
  · intro j hj
    exact ⟨path_to_word_legal x n hx hn j hj, word_to_path_to_word x n hx hn j hj⟩

end ExternalBridgePressureWordPhysical
