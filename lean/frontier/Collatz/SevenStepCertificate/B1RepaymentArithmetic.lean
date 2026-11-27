import Collatz.SevenStepCertificate.Basic

/-! Strict repayment after an arbitrary positive number of growing B1 laps. -/
namespace Collatz.SevenStepCertificate

/-- The contraction budget dominates twice the remaining growth factor. -/
theorem b1_repayment_power_gap (h : Nat) (hh : 0 < h) :
    2 * 6561 ^ h ≤ 16384 ^ h := by
  cases h with
  | zero => omega
  | succ h =>
      have lower := Nat.pow_le_pow_left (by decide : 6561 ≤ 16384) h
      simp only [Nat.pow_succ] at *
      omega

/-- The exact initial and terminal counter equations imply a strict decrease
in the original B1 parameter, uniformly over both unbounded parameters. -/
theorem b1_repayment_strict_parameter_drop (h q r t : Nat)
    (hh : 0 < h) (hr : 0 < r)
    (initial : 601*t+151 = 128^h*q)
    (terminal : 729^h*q = 601*(1+131072*128^h*r)+151) :
    1+131072*9^h*r < t := by
  have square : 128^h * 128^h = 16384^h := by
    simpa using (Nat.mul_pow 128 128 h).symm
  have product : 729^h * 9^h = 6561^h := by
    simpa using (Nat.mul_pow 729 9 h).symm
  have eliminated :
      729^h*(601*t+151) = 78774272*16384^h*r+752*128^h := by
    calc
      729^h*(601*t+151) = 729^h*(128^h*q) := by rw [initial]
      _ = 128^h*(729^h*q) := by ac_rfl
      _ = 128^h*(601*(1+131072*128^h*r)+151) := by rw [terminal]
      _ = (601*131072)*(128^h*128^h)*r+(601+151)*128^h := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
        ac_rfl
      _ = 78774272*16384^h*r+752*128^h := by rw [square]
  have lower : 729^h ≤ 6561^h*r := by
    have first := Nat.pow_le_pow_left (by decide : 729 ≤ 6561) h
    have second := Nat.mul_le_mul_left (6561^h) (by omega : 1 ≤ r)
    simp only [Nat.mul_one] at second
    exact Nat.le_trans first second
  have positive : 0 < 6561^h*r := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 6561)) hr
  have small := Nat.mul_le_mul_left 752 lower
  have large := Nat.mul_lt_mul_of_pos_right (by decide : 752 < 78774272) positive
  have excess : 752*729^h < 78774272*6561^h*r := by
    simp only [Nat.mul_assoc] at *
    omega
  have doubled := Nat.mul_le_mul_left 78774272
    (Nat.mul_le_mul_right r (b1_repayment_power_gap h hh))
  have growth : 2*(78774272*6561^h*r) ≤ 78774272*16384^h*r := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using doubled
  have target :
      729^h*(601*(1+131072*9^h*r)+151) =
        78774272*6561^h*r+752*729^h := by
    calc
      729^h*(601*(1+131072*9^h*r)+151) =
          (601*131072)*(729^h*9^h)*r+(601+151)*729^h := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
        ac_rfl
      _ = 78774272*6561^h*r+752*729^h := by rw [product]
  have scaled :
      729^h*(601*(1+131072*9^h*r)+151) < 729^h*(601*t+151) := by
    rw [target, eliminated]
    omega
  have affine := Nat.lt_of_mul_lt_mul_left scaled
  omega

end Collatz.SevenStepCertificate
