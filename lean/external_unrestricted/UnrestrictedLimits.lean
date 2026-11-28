import UnrestrictedCountBound
import UnrestrictedRotation
import BridgeRungs
import Mathlib.Analysis.SpecificLimits.Basic

/-! Full-sequence normalized count bounds and limits. The limsup and nonlimit
helpers expose their exact remaining premises; no unfinished injection is imported. -/
namespace ExternalM4UnrestrictedLimits
open ExternalFiniteBridgeDraft ExternalM4UnrestrictedDraft
open ExternalM4UnrestrictedCounts ExternalM4UnrestrictedCountBound
open ExternalM4UnrestrictedRotation ExternalFiniteBridgeRungs
open Filter
open scoped Topology

theorem normalized_log_zero : normalizedLogCount 0 = 0 := by
  simp [normalizedLogCount]

theorem normalized_log_bounds : NormalizedLogBounds := by
  refine ⟨normalized_log_zero, fun r => ?_⟩
  by_cases hr : r = 0
  · subst r
    rw [normalized_log_zero]
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
    exact ⟨le_rfl, by positivity⟩
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hrreal : (0 : ℝ) < r := Nat.cast_pos.mpr hrpos
  have hc : (1 : ℝ) ≤ count r := by exact_mod_cast count_pos r hrpos
  have hlog : 0 ≤ Real.log (count r : ℝ) := Real.log_nonneg hc
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  constructor
  · exact div_nonneg (div_nonneg hlog h10.le) hrreal.le
  · have hu : (count r : ℝ) ≤ (2 : ℝ) ^ (2 * r) := by
      exact_mod_cast count_upper r
    have hl := Real.log_le_log (lt_of_lt_of_le zero_lt_one hc) hu
    rw [Real.log_pow] at hl
    unfold normalizedLogCount
    calc
      (Real.log (count r : ℝ) / Real.log 10) / (r : ℝ) ≤
          (((2 * r : ℕ) : ℝ) * Real.log 2 / Real.log 10) / (r : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hl h10.le) hrreal.le
      _ = 2 * (Real.log 2 / Real.log 10) := by
        push_cast
        field_simp

theorem normalized_log_bounded_above :
    atTop.IsBoundedUnder (· ≤ ·) normalizedLogCount :=
  isBoundedUnder_of ⟨2 * (Real.log 2 / Real.log 10), fun r =>
    (normalized_log_bounds.2 r).2⟩

theorem normalized_log_bounded_below :
    atTop.IsBoundedUnder (· ≥ ·) normalizedLogCount :=
  isBoundedUnder_of ⟨0, fun r => (normalized_log_bounds.2 r).1⟩

theorem normalized_log_zero_frequently :
    ∃ᶠ r : ℕ in atTop, normalizedLogCount r ≤ 0 := by
  apply frequently_atTop.mpr
  intro R
  obtain ⟨r,hr,hrung⟩ := source_rungs_unbounded R
  refine ⟨r,hr.le,?_⟩
  simp [normalizedLogCount,rung_count_one r hrung]

theorem normalized_log_liminf : NormalizedLogLiminf := by
  apply le_antisymm
  · exact liminf_le_of_frequently_le normalized_log_zero_frequently normalized_log_bounded_below
  · exact le_liminf_of_le normalized_log_bounded_above.isCoboundedUnder_ge
      (Eventually.of_forall fun r => (normalized_log_bounds.2 r).1)

theorem quotient_eighth_tendsto :
    Tendsto (fun r : ℕ => ((r / 8 : ℕ) : ℝ) / (r : ℝ)) atTop (nhds (1 / 8 : ℝ)) := by
  have hm := tendsto_mod_div_atTop_nhds_zero_nat (m := 8) (by decide)
  have hh' : Tendsto (fun r : ℕ => (1 - ((r % 8 : ℕ) : ℝ) / (r : ℝ)) / 8)
      atTop (nhds (1 / 8 : ℝ)) := by
    simpa using ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hm).div_const (8 : ℝ)
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have he : ((r % 8 : ℕ) : ℝ) + 8 * ((r / 8 : ℕ) : ℝ) = (r : ℝ) := by
    exact_mod_cast Nat.mod_add_div r 8
  field_simp
  nlinarith

noncomputable def exponentialScore (r : ℕ) : ℝ :=
  ((r / 8 : ℕ) : ℝ) / (r : ℝ) * (Real.log 2 / Real.log 10)

theorem exponential_score_tendsto :
    Tendsto exponentialScore atTop (nhds ((Real.log 2 / Real.log 10) / 8)) := by
  have h := quotient_eighth_tendsto.mul_const (Real.log 2 / Real.log 10)
  convert h using 1 <;> first | rfl | ring

theorem exponential_score_le (h : ExponentialCountLower) (r : ℕ) (hr : 8 ≤ r)
    (hd : (1 / 2 : ℝ) ≤ defect slope r) : exponentialScore r ≤ normalizedLogCount r := by
  have hc : (2 : ℝ) ^ (r / 8) ≤ (count r : ℝ) := by exact_mod_cast h r hr hd
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (r / 8)) hc
  rw [Real.log_pow] at hl
  unfold exponentialScore normalizedLogCount
  calc
    ((r / 8 : ℕ) : ℝ) / (r : ℝ) * (Real.log 2 / Real.log 10) =
        (((r / 8 : ℕ) : ℝ) * Real.log 2 / Real.log 10) / (r : ℝ) := by ring
    _ ≤ (Real.log (count r : ℝ) / Real.log 10) / (r : ℝ) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hl (Real.log_nonneg (by norm_num))) (Nat.cast_nonneg r)

theorem large_defects_frequently :
    ∃ᶠ r : ℕ in atTop, 8 ≤ r ∧ (1 / 2 : ℝ) ≤ defect slope r := by
  apply frequently_atTop.mpr
  intro R
  obtain ⟨r,hr,hd⟩ := large_defects_unbounded (max R 8)
  exact ⟨r,by omega,by omega,hd⟩

theorem normalized_log_limsup_of_exponential_count_lower
    (h : ExponentialCountLower) : NormalizedLogLimsup := by
  apply le_limsup_of_le normalized_log_bounded_above
  intro b hb
  apply le_of_tendsto_of_frequently exponential_score_tendsto
  exact (large_defects_frequently.and_eventually hb).mono fun r hh =>
    (exponential_score_le h r hh.1.1 hh.1.2).trans hh.2

theorem no_all_length_limit_of_limsup (h : NormalizedLogLimsup) : NoAllLengthLimit := by
  rintro ⟨L,hL⟩
  have hz : L = 0 := hL.liminf_eq.symm.trans normalized_log_liminf
  have hs : (Real.log 2 / Real.log 10) / 8 ≤ L := hL.limsup_eq ▸ h
  have hp : (0 : ℝ) < (Real.log 2 / Real.log 10) / 8 :=
    div_pos (div_pos (Real.log_pos (by norm_num)) (Real.log_pos (by norm_num))) (by norm_num)
  linarith

theorem no_all_length_limit_of_exponential_count_lower
    (h : ExponentialCountLower) : NoAllLengthLimit :=
  no_all_length_limit_of_limsup (normalized_log_limsup_of_exponential_count_lower h)

end ExternalM4UnrestrictedLimits
