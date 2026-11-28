import BridgeArithmetic
import BridgeEncoding
import BridgeRewards

/-! The exact finite maximum, its uniqueness, and the zero-length convention. -/
namespace ExternalFiniteBridgeExtremal
open ExternalFiniteBridgeDraft ExternalFiniteBridgeArithmetic
open ExternalFiniteBridgeEncoding ExternalFiniteBridgeRewards
open scoped BigOperators

theorem floorPrefix_positive (r : ℕ) : PositivePrefix r (floorPrefix slope r) := by
  refine ⟨?_, fun i => ?_⟩
  · simp [floorPrefix, floorAt]
  · exact unit_floor_increments slope (le_of_lt source_slope_facts.1) i.val

theorem raiseLast_positive (r : ℕ) (w : Word r) (hw : PositiveWord r w) :
    PositiveWord r (raiseLast r w) := by
  intro i
  have hi := hw i
  unfold raiseLast
  split_ifs <;> omega

theorem raiseLast_prefix_last (r : ℕ) (hr : 0 < r) (w : Word r) :
    wordPrefix r (raiseLast r w) (Fin.last r) = wordPrefix r w (Fin.last r) + 1 := by
  let i : Fin r := ⟨r - 1, by omega⟩
  have hi : i.val + 1 = r := by dsimp [i]; omega
  have he : i.succ = Fin.last r := Fin.ext hi
  rw [← he, wordPrefix_step, raiseLast_prefix_open]
  simp only [raiseLast, hi, ite_true, Nat.cast_add, Nat.cast_one]
  rw [wordPrefix_step]
  ring

theorem mechanical_prefix_open (r : ℕ) (t : Fin r) :
    wordPrefix r (mechanicalWord slope r) t.castSucc = floorAt slope t.val := by
  unfold mechanicalWord
  rw [raiseLast_prefix_open, wordPrefix_prefixLetters r _ (floorPrefix_positive r)]
  rfl

theorem mechanical_source (r : ℕ) (hr : StrictRung slope r) :
    SourceWord slope r (mechanicalWord slope r) := by
  refine ⟨hr.1, ?_, ?_, ?_⟩
  · exact raiseLast_positive r _ (prefixLetters_positive r _ (floorPrefix_positive r))
  · unfold mechanicalWord
    rw [raiseLast_prefix_last r hr.1, wordPrefix_prefixLetters r _ (floorPrefix_positive r)]
    change floorAt slope r + 1 = Int.ceil ((r : ℝ) * slope)
    exact (nonintegral_endpoint slope r (source_slope_nonintegral r hr.1)).symm
  · intro t
    rw [mechanical_prefix_open, strict_rung_caps slope r hr t.val t.isLt]

theorem mechanical_reward (r : ℕ) :
    reward r (mechanicalWord slope r) = phaseZeroReference slope r := by
  rw [← reward_real_power r (mechanicalWord slope r)]
  unfold powerReward phaseZeroReference
  apply Finset.sum_congr rfl
  intro t _
  rw [mechanical_prefix_open]

theorem source_prefix_le_floor (r : ℕ) (hr : StrictRung slope r) (w : Word r)
    (hw : SourceWord slope r w) (t : Fin r) :
    wordPrefix r w t.castSucc ≤ floorAt slope t.val := by
  simpa only [strict_rung_caps slope r hr t.val t.isLt] using hw.2.2.2 t

theorem source_reward_term_le (r : ℕ) (hr : StrictRung slope r) (w : Word r)
    (hw : SourceWord slope r w) (t : Fin r) :
    Real.rpow 2 ((wordPrefix r w t.castSucc : ℝ) - (t.val : ℝ) * slope) ≤
      Real.rpow 2 ((floorAt slope t.val : ℝ) - (t.val : ℝ) * slope) := by
  simp only [Real.rpow_eq_pow]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  exact sub_le_sub_right (Int.cast_le.mpr (source_prefix_le_floor r hr w hw t)) _

theorem source_reward_le_reference (r : ℕ) (hr : StrictRung slope r) (w : Word r)
    (hw : SourceWord slope r w) : reward r w ≤ phaseZeroReference slope r := by
  rw [← reward_real_power r w]
  unfold powerReward phaseZeroReference
  exact Finset.sum_le_sum (fun t _ => source_reward_term_le r hr w hw t)

theorem phase_zero_extremizer : PhaseZeroExtremizer := by
  intro r hr
  exact ⟨mechanical_source r hr, mechanical_reward r,
    fun w hw => source_reward_le_reference r hr w hw⟩

theorem prefix_equality_of_reward_equality (r : ℕ) (hr : StrictRung slope r)
    (w : Word r) (hw : SourceWord slope r w)
    (he : reward r w = phaseZeroReference slope r) :
    ∀ t : Fin r, wordPrefix r w t.castSucc = floorAt slope t.val := by
  rw [← reward_real_power r w] at he
  unfold powerReward phaseZeroReference at he
  have hp := (Finset.sum_eq_sum_iff_of_le
    (fun t _ => source_reward_term_le r hr w hw t)).mp he
  intro t
  have ht := hp t (Finset.mem_univ t)
  simp only [Real.rpow_eq_pow] at ht
  have hx := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)).mp ht
  exact_mod_cast (show (wordPrefix r w t.castSucc : ℝ) = (floorAt slope t.val : ℝ) by linarith)

theorem unique_extremizer : UniqueExtremizer := by
  intro r hr w hw
  constructor
  · intro he
    have hopen := prefix_equality_of_reward_equality r hr w hw he
    have hfull : wordPrefix r w = wordPrefix r (mechanicalWord slope r) := by
      funext t
      refine Fin.lastCases ?_ (fun i => ?_) t
      · exact hw.2.2.1.trans (mechanical_source r hr).2.2.1.symm
      · rw [hopen i, mechanical_prefix_open]
    have hletters := congrArg (prefixLetters r) hfull
    simpa only [prefixLetters_wordPrefix] using hletters
  · rintro rfl
    exact mechanical_reward r

theorem zero_length_convention : ZeroLengthConvention := by
  constructor
  · intro w
    simp [SourceWord, FloorWord, reward]
  · intro J
    constructor
    · intro hJ
      funext t
      have ht : t = 0 := by
        apply Fin.ext
        have hi := t.isLt
        simp only [Fin.val_zero]
        omega
      simpa only [ht] using hJ.1
    · rintro rfl
      simp [DepthBridge]

end ExternalFiniteBridgeExtremal
