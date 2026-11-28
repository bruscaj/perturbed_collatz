import DepthOneSeries
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.IntervalCases

/-! Exact certificate for the candidate series, without an infimum assumption. -/
namespace ExternalO3DepthOneNumerics
open ExternalO3Spec ExternalO3DepthOneSeries
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable def alpha : ℝ := ascent / Real.log 2

theorem alpha_lower : (31 : ℝ) / 53 < alpha := by
  have hp : (2 : ℝ) ^ 84 < (3 : ℝ) ^ 53 := by norm_num
  have hl := Real.log_lt_log (pow_pos (by norm_num : (0 : ℝ) < 2) 84) hp
  simp only [Real.log_pow] at hl
  unfold alpha
  apply (lt_div_iff₀ log_two_pos).mpr
  rw [ascent_eq]
  norm_num at hl
  linarith

theorem alpha_upper : alpha < (24 : ℝ) / 41 := by
  have hp : (3 : ℝ) ^ 41 < (2 : ℝ) ^ 65 := by norm_num
  have hl := Real.log_lt_log (pow_pos (by norm_num : (0 : ℝ) < 3) 41) hp
  simp only [Real.log_pow] at hl
  unfold alpha
  apply (div_lt_iff₀ log_two_pos).mpr
  rw [ascent_eq]
  norm_num at hl
  linarith

def floorValues : List ℕ :=
  [1, 2, 2, 3, 3, 4, 5, 5, 6, 6, 7, 8, 8, 9, 9, 10, 10, 11, 12, 12,
   13, 13, 14, 15, 15, 16, 16, 17, 17, 18, 19, 19, 20, 20, 21, 22, 22,
   23, 23, 24, 24, 25, 26, 26, 27, 27, 28, 29, 29, 30, 30, 31, 32, 32,
   33, 33, 34, 34, 35, 36, 36, 37, 37, 38, 39, 39, 40, 40, 41, 41, 42,
   43, 43, 44, 44, 45, 46, 46, 47, 47]

def certifiedFloor (r : ℕ) : ℕ := (floorValues[r - 1]?).getD 0

theorem certificate_lower (r : ℕ) (hr : 1 ≤ r) (h80 : r ≤ 80) :
    (certifiedFloor r : ℝ) ≤ 1 + (r : ℝ) * ((31 : ℝ) / 53) := by
  interval_cases r <;> norm_num [certifiedFloor, floorValues]

theorem certificate_upper (r : ℕ) (hr : 1 ≤ r) (h80 : r ≤ 80) :
    1 + (r : ℝ) * ((24 : ℝ) / 41) ≤ (certifiedFloor r : ℝ) + 1 := by
  interval_cases r <;> norm_num [certifiedFloor, floorValues]

theorem certified_floor_correct (r : ℕ) (hr : 1 ≤ r) (h80 : r ≤ 80) :
    floorThreshold r = (certifiedFloor r : ℤ) := by
  change Int.floor (1 + (r : ℝ) * alpha) = (certifiedFloor r : ℤ)
  apply Int.floor_eq_iff.mpr
  simp only [Int.cast_natCast]
  have hp : (0 : ℝ) < r := by exact_mod_cast hr
  have hlo := mul_lt_mul_of_pos_left alpha_lower hp
  have hhi := mul_lt_mul_of_pos_left alpha_upper hp
  have hcl := certificate_lower r hr h80
  have hcu := certificate_upper r hr h80
  constructor <;> linarith

noncomputable def seriesLower : ℝ :=
  24353541309990355464286619961554936997 / 170141183460469231731687303715884105728

noncomputable def seriesUpper : ℝ :=
  24353541309990355464286690330299114661 / 170141183460469231731687303715884105728

theorem partial_80_exact : depthOnePartial 80 = seriesLower := by
  unfold depthOnePartial
  calc
    (∑ r ∈ Finset.range 80, depthOneTerm (r + 1)) =
        ∑ r ∈ Finset.range 80,
          (2 : ℝ) ^ (-((r + 1 : ℕ) : ℤ)) *
            ((1 : ℝ) / 2 - (2 : ℝ) ^ (-(certifiedFloor (r + 1) : ℤ))) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hlt : r < 80 := Finset.mem_range.mp hr
      rw [term_eq, certified_floor_correct (r + 1) (by omega) (by omega)]
    _ = seriesLower := by
      norm_num [Finset.sum_range_succ, certifiedFloor, floorValues, seriesLower]

theorem series_enclosure : seriesLower ≤ depthOneSeries ∧ depthOneSeries ≤ seriesUpper := by
  have ht := depth_one_tail 80
  rw [partial_80_exact] at ht
  norm_num [seriesLower, seriesUpper] at ht ⊢
  constructor <;> linarith

theorem series_upper_strict : depthOneSeries < seriesUpper := by
  have ht := depth_one_tail_strict 80
  rw [partial_80_exact] at ht
  norm_num [seriesLower, seriesUpper] at ht ⊢
  linarith

theorem enclosure_width : seriesUpper - seriesLower = (2 : ℝ) ^ (-81 : ℤ) := by
  norm_num [seriesUpper, seriesLower]

end ExternalO3DepthOneNumerics
