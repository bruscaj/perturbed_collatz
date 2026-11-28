import PressureExpectedTypes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact finite phase arithmetic for the frozen pressure definitions. No
pressure limit, approximation, Challenge or critical-law model is imported. -/
namespace ExternalBridgePressurePhase
open ExternalFiniteBridgeDraft ExternalBridgePressureDraft

theorem slope_gt_one : (1 : ℝ) < slope := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold slope
  apply (lt_div_iff₀ h2).mpr
  simpa using Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)

theorem slope_lt_two : slope < (2 : ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold slope
  apply (div_lt_iff₀ h2).mpr
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (3 : ℝ) < 2 ^ 2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem phase_floor_zero (x : ℝ) : phaseFloor x 0 = 0 := by
  simp [phaseFloor]

theorem phase_shift_bounds (x : ℝ) (m : ℕ) :
    0 ≤ phaseShift x m ∧ phaseShift x m < 1 :=
  ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩

theorem phase_floor_add (x : ℝ) (m n : ℕ) :
    phaseFloor x (m+n) = phaseFloor x m + phaseFloor (phaseShift x m) n := by
  have he : Int.fract (x+(m : ℝ)*slope)+(n : ℝ)*slope =
      (x+((m+n : ℕ) : ℝ)*slope)-(Int.floor (x+(m : ℝ)*slope) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  simp only [phaseFloor,phaseShift,phaseTick,Int.floor_fract,sub_zero]
  rw [he,Int.floor_sub_intCast]
  omega

theorem phase_tick_add (x : ℝ) (m n : ℕ) :
    phaseTick x (m+n) = phaseTick (phaseShift x m) n := by
  simp only [phaseTick,phaseShift]
  rw [Int.fract_fract_add]
  congr 1
  push_cast
  ring

theorem phase_increment_alphabet (x : ℝ) (t : ℕ) :
    phaseIncrement x t = 1 ∨ phaseIncrement x t = 2 := by
  have hlo : x+(t : ℝ)*slope+1 ≤ x+((t+1 : ℕ) : ℝ)*slope := by
    push_cast
    linarith [slope_gt_one]
  have hhi : x+((t+1 : ℕ) : ℝ)*slope ≤ x+(t : ℝ)*slope+2 := by
    push_cast
    linarith [slope_lt_two]
  have hl := Int.floor_mono hlo
  have hu := Int.floor_mono hhi
  simp only [Int.floor_add_one] at hl
  simp only [Int.floor_add_ofNat] at hu
  unfold phaseIncrement phaseFloor
  omega

theorem phase_cocycle : PhaseCocycle := by
  intro x _ _ m n
  exact ⟨(phase_shift_bounds x m).1,(phase_shift_bounds x m).2,
    phase_floor_add x m n,phase_tick_add x m n,phase_increment_alphabet x n⟩

end ExternalBridgePressurePhase
