import CriticalSpaceExpectedTypes
import Mathlib.Tactic.Ring

/-! Literal circle representatives and integer shifts, with the original
configuration topology and Borel sigma algebra. No stationary law is assumed. -/
namespace ExternalCriticalSpaceArithmetic
open ExternalCriticalSpaceDraft ExternalFiniteBridgeDraft
open MeasureTheory

theorem representative_bounds (x : Phase) :
    0 ≤ phaseRepresentative x ∧ phaseRepresentative x < 1 := by
  simpa only [phaseRepresentative, Set.mem_Ico, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem representative_coe (x : Phase) : ((phaseRepresentative x : ℝ) : Phase) = x := by
  exact AddCircle.coe_equivIco

theorem representative_fract (a : ℝ) : phaseRepresentative (a : Phase) = Int.fract a := by
  simp [phaseRepresentative, AddCircle.coe_equivIco_mk_apply]

theorem phase_representative_law : PhaseRepresentativeLaw := by
  exact ⟨fun x => ⟨(representative_bounds x).1,(representative_bounds x).2,representative_coe x⟩,
    representative_fract⟩

theorem time_shift_zero (w : Config) : timeShift 0 w = w := by
  simp [timeShift]

theorem time_shift_add (s t : ℤ) (w : Config) :
    timeShift s (timeShift t w) = timeShift (s+t) w := by
  have he : (((s+t : ℤ) : ℝ)*slope) = (t : ℝ)*slope+(s : ℝ)*slope := by
    push_cast
    ring
  simp only [timeShift,he]
  simp [add_assoc]

theorem time_shift_continuous (s : ℤ) : Continuous (timeShift s) := by
  apply Continuous.prodMk
  · exact continuous_fst.add continuous_const
  · apply continuous_pi
    intro t
    exact (continuous_apply (t+s)).comp continuous_snd

theorem time_shift_measurable (s : ℤ) : Measurable (timeShift s) :=
  (time_shift_continuous s).measurable

theorem shift_group_and_continuity : ShiftGroupAndContinuity := by
  exact ⟨time_shift_zero,time_shift_add,fun s => ⟨time_shift_continuous s,time_shift_measurable s⟩⟩

end ExternalCriticalSpaceArithmetic
