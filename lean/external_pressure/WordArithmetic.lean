import PressureWordExpectedTypes
import PhaseCocycle
import BridgeEncoding

/-! Finite auxiliary cap and overridden canonical-profile arithmetic only. -/
namespace ExternalBridgePressureWordArithmetic
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft ExternalBridgePressureWordDraft
open ExternalBridgePressurePhase ExternalFiniteBridgeEncoding
open scoped BigOperators

theorem zero_volume_convention : ZeroVolumeConvention := by
  intro x lam
  simp [AuxWord, auxReward, auxPartition, auxFinitePartition, auxLogPartition,
    auxLogPressure]

theorem aux_cap_increment (x : ℝ) (t : ℕ) :
    auxCap x (t+1) - auxCap x t = 1 ∨ auxCap x (t+1) - auxCap x t = 2 := by
  simpa [phaseIncrement, phaseFloor, auxCap] using phase_increment_alphabet x t

theorem aux_cap_upper (x : ℝ) (hx : ClosedPhase x) (n : ℕ) (hn : 1 ≤ n) :
    auxCap x n ≤ (2*n : ℕ) := by
  have hs := slope_lt_two
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h : x + (n : ℝ)*slope < (2*n+1 : ℕ) := by
    push_cast
    nlinarith [hx.2]
  have hfloor := Int.floor_lt.mpr h
  exact_mod_cast (show auxCap x n ≤ (2*n : ℕ) by
    unfold auxCap
    exact Int.lt_add_one_iff.mp (by exact_mod_cast hfloor))

theorem cap_increment_bounds : CapIncrementBounds := by
  intro x hx
  exact ⟨aux_cap_increment x, aux_cap_upper x hx⟩

theorem canonical_profile_positive (x : ℝ) (n : ℕ) (hx : ClosedPhase x) :
    PositivePrefix n (canonicalProfile x n) := by
  refine ⟨by simp [canonicalProfile], fun i => ?_⟩
  by_cases hi : i.val = 0
  · have hs : (1 : ℝ) ≤ x + (1 : ℕ)*slope := by
      simp only [Nat.cast_one, one_mul]
      linarith [slope_gt_one, hx.1]
    have hf : (1 : ℤ) ≤ auxCap x 1 := by
      simpa [auxCap] using (Int.le_floor.mpr (by simpa using hs) : (1 : ℤ) ≤ Int.floor (x+(1:ℕ)*slope))
    simpa [canonicalProfile, hi] using hf
  · have h := aux_cap_increment x i.val
    simp only [canonicalProfile, Fin.val_castSucc, Fin.val_succ, hi, ite_false,
      Nat.add_eq_zero_iff, one_ne_zero, and_false]
    omega

theorem canonical_word_law : CanonicalWordLaw := by
  intro x n hx
  have hp := canonical_profile_positive x n hx
  have he : wordPrefix n (canonicalWord x n) = canonicalProfile x n :=
    wordPrefix_prefixLetters n _ hp
  refine ⟨hp, he, fun hn => ?_⟩
  refine ⟨hn, prefixLetters_positive n _ hp, ?_, ?_⟩
  · rw [he]
    simp [canonicalProfile, Nat.ne_of_gt hn]
  · intro t
    rw [he]
    by_cases ht : t.val = 0
    · have h : (0 : ℤ) ≤ auxCap x 0 := by
        simpa [auxCap] using (Int.floor_nonneg.mpr hx.1)
      simpa [canonicalProfile, ht] using h
    · simp [canonicalProfile, ht]

end ExternalBridgePressureWordArithmetic
