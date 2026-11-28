import DepthOneSeries
import Arithmetic
import Mathlib.NumberTheory.Real.Irrational

/-! Source-specific irrationality from the distinct prime powers 2 and 3. -/
namespace ExternalO3LogRatio
open ExternalO3DepthOneSeries

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem ascent_ratio_irrational : Irrational (ascent / Real.log 2) := by
  rintro ⟨q, hq⟩
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by
    rw [hq]
    exact le_of_lt (div_pos ascent_pos log_two_pos)
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hqR
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hnumCast : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hden : (0 : ℝ) < (q.den : ℝ) := Nat.cast_pos.mpr q.den_pos
  have heq : ascent / Real.log 2 = (q.num.toNat : ℝ) / (q.den : ℝ) := by
    rw [← hq, Rat.cast_def, hnumCast]
  have hmul : ascent * (q.den : ℝ) = (q.num.toNat : ℝ) * Real.log 2 :=
    (div_eq_div_iff (ne_of_gt log_two_pos) (ne_of_gt hden)).mp heq
  have hl : (q.den : ℝ) * Real.log 3 =
      ((q.num.toNat + q.den : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_add]
    rw [ascent_eq] at hmul
    nlinarith
  have hp : (3 : ℝ) ^ q.den = (2 : ℝ) ^ (q.num.toNat + q.den) := by
    apply Real.log_injOn_pos (pow_pos (by norm_num : (0 : ℝ) < 3) _)
      (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    simpa only [Real.log_pow] using hl
  have hpNat : (3 : ℕ) ^ q.den = 2 ^ (q.num.toNat + q.den) := by exact_mod_cast hp
  have hv := congrArg (padicValNat 2) hpNat
  have hthree : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by decide)
  have htwo : padicValNat 2 2 = 1 := padicValNat_self
  simp only [padicValNat.pow, hthree, htwo, mul_zero, mul_one] at hv
  have := q.den_pos
  omega

end ExternalO3LogRatio
